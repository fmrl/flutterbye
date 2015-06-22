// $legal:614:
// 
// Copyright 2015 Michael Lowell Roberts
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 
// ,$

//@requires "seq.fst"
//@requires "set.fst"

module Tesseract.Specs.Tesseract

   type step_g (region_t: Type) (state_t: Type) (step_kind_t: Type)
      = region_t 
         -> state_t
         -> step_kind_t 
         -> Tot (state_t * (Seq.seq_g (region_t * step_kind_t)))

   type effect_g (region_t: Type) (state_t: Type) (step_kind_t: Type) 
      =
      | Spawn: 
         region: region_t 
         -> state0: state_t
         -> step: step_g region_t state_t step_kind_t
         -> effect_g region_t state_t step_kind_t
      | Step: 
         region: region_t 
         -> step_kind: step_kind_t 
         -> effect_g region_t state_t step_kind_t

   type _tesseract_g 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      = Seq.seq_g (effect_g region_t state_t step_kind_t)

   val _domain: 
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> _tesseract_g region_t state_t step_kind_t
      -> Tot (option (Set.set_g region_t))
   let _domain
      (region_t: Type)
      (state_t: Type)
      (step_kind_t: Type)
      _tess
      = let on_fold 
         = (fun accum (pair: (Seq.index_g _tess * effect_g region_t state_t step_kind_t))
            -> match accum with
                  | None ->
                     // an unsafe tesseract continues to be unsafe.
                     None
                  | Some set ->
                     // examine the next effect in the sequence.
                     (match pair with
                        | (_, Spawn region _ _) ->
                           // if we're looking at a spawn effect associated with a region, that region must not have already set.
                           if Set.is_mem set region then
                              None
                           // otherwise, note that we have encountered it.
                           else
                              Some (Set.add set region)
                        | (_, Step region _) ->
                           // a step effect associated with a given region must be in our set of set regions.
                           if Set.is_mem set region then
                              accum
                           else
                              None))
         in (Seq.foldl _tess on_fold (Some Set.empty))

   val _is_tesseract_safe: 
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> _tesseract_g region_t state_t step_kind_t 
      -> Tot bool
   let _is_tesseract_safe 
      (region_t: Type)
      (state_t: Type)
      (step_kind_t: Type)
      (_tess: _tesseract_g region_t state_t step_kind_t)
      = is_Some (_domain _tess)

   type tesseract_g 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      = _tess: 
         _tesseract_g 
            region_t 
            state_t 
            step_kind_t{_is_tesseract_safe _tess}

   val init:
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> Tot (tesseract_g region_t state_t step_kind_t)
   let init 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      = Seq.empty

   val domain: 
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> tesseract_g region_t state_t step_kind_t
      -> Tot (Set.set_g region_t)
   let domain
      (region_t: Type)
      (state_t: Type)
      (step_kind_t: Type)
      tess
      = match _domain tess with
         | Some d ->
            d

   val is_mem:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> tesseract_g region_t state_t step_kind_t
      -> region_t
      -> Tot bool
   let is_mem 
      (region_t: Type) 
      (step_kind_t: Type) 
      tess 
      region
      = Set.is_mem (domain tess) region

   val lookup:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> tess: tesseract_g region_t state_t step_kind_t
      -> region: region_t{is_mem tess region}
      -> Tot (Seq.seq_g (effect_g region_t state_t step_kind_t))
   let lookup
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      tess 
      region
      = Seq.filter
            (fun event ->
               match event with
                  | Spawn r _ _ ->
                     r = region
                  | Step r _ ->
                     r = region)
            tess

   val __spawn_safety_property:
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> tess: tesseract_g region_t state_t step_kind_t 
      -> region: region_t{not (is_mem tess region)}
      -> state0: state_t
      -> step: step_g region_t state_t step_kind_t
      -> Lemma
         (ensures (_is_tesseract_safe (Seq.append tess (Spawn region state0 step))))
   let __spawn_safety_property 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      tess 
      region
      state0
      step
      = admit ()

   val spawn:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> tess: tesseract_g region_t state_t step_kind_t
      -> region: region_t{not (is_mem tess region)}
      -> state_t
      -> step_g region_t state_t step_kind_t
      -> Tot (tesseract_g region_t state_t step_kind_t)
   let spawn
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      tess 
      region
      state0
      step
      = 
         (__spawn_safety_property tess region state0 step);
         Seq.append tess (Spawn region state0 step)

   val __step_safety_property:
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> tess: tesseract_g region_t state_t step_kind_t 
      -> region: region_t{is_mem tess region}
      -> step_kind: step_kind_t
      -> Lemma
         (ensures (_is_tesseract_safe (Seq.append tess (Step region step_kind))))
   let __step_safety_property 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      tess 
      region
      step_kind
      = admit ()

   val step:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> tess: tesseract_g region_t state_t step_kind_t
      -> region: region_t{is_mem tess region}
      -> step_kind_t
      -> Tot (tesseract_g region_t state_t step_kind_t)
   let step
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      tess 
      region
      step_kind
      = 
         (__step_safety_property tess region step_kind);
         Seq.append tess (Step region step_kind)
      
// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
