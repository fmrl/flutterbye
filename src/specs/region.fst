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

//@requires "effects.fst"

module Tesseract.Specs.Region

   type _region_g 'state 'step_kind
      = {
         id: Effects.region_id_t;
         effect_log: Effects._log_g 'state 'step_kind
      }

   val __region_safety: 
      #state_t: Type 
      -> #step_kind_t: Type 
      -> Effects._log_g state_t step_kind_t 
      -> Effects.region_id_t
      -> Tot bool
   let rec __region_safety
      (state_t: Type)
      (step_kind_t: Type)
      _log
      region_id
      =  // empty regions don't exist.
         (1 < Seq.length _log) 
         // the first effect must be a spawn effect.
         && (Effects.is_Spawn (Seq.nth _log 0))
         && ((1 = Seq.length _log)
            || // the remainder of the effect log consists
               // only of step effects for the specified
               // region
               (let tail = Seq.remove _log 0 in
               let f 
                  = fun (safe: bool) (index: Seq.index_g tail)
                     -> (if safe then
                           (match Seq.nth tail index with
                              | Effects.Spawn _ _ ->
                                 false
                              | Effects.Step n _ ->
                                 if region_id = n then
                                    true
                                 else
                                    false)
                           else
                              false) in
               (Seq.foldl tail f true))
               // inductive on items 1..n.
               && (__region_safety 
                     (Seq.slice 
                        _log 
                        0 
                        (Seq.length _log - 1))
                     region_id))

   type region_g 
      (state_t: Type) 
      (step_kind_t: Type) 
      = _region: 
            _region_g
               state_t 
               step_kind_t{__region_safety _region.effect_log _region.id}

   val spawn:
      #state_t: Type
      -> #step_kind_t: Type
      -> region_g state_t step_kind_t
      -> Tot (ffct: Effects.effect_g state_t step_kind_t{Effects.is_Spawn ffct})
   let spawn  
      (state_t: Type) 
      (step_kind_t: Type) 
      region
      =  Seq.nth region.effect_log 0

   val state0:
      #state_t: Type
      -> #step_kind_t: Type
      -> region_g state_t step_kind_t
      -> Tot state_t
   let state0  
      (state_t: Type) 
      (step_kind_t: Type) 
      region
      = Effects.Spawn.state0 (spawn region)

   val step:
      #state_t: Type
      -> #step_kind_t: Type
      -> region_g state_t step_kind_t
      -> Tot (Effects.step_g state_t step_kind_t)
   let step  
      (state_t: Type) 
      (step_kind_t: Type) 
      region
      = Effects.Spawn.step (spawn region)

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
