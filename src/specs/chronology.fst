// $legal:322:
// 
// This work is licensed under the Creative Commons
// Attribution-NonCommercial-ShareAlike 4.0 International
// License. To view a copy of this license, visit
// http://creativecommons.org/licenses/by-nc-sa/4.0/
// or send a letter to:
// 
// Creative Commons
// PO Box 1866
// Mountain View, CA 94042
// USA
// 
// ,$

//@requires "seq.fst"
//@requires "set.fst"

module Tesseract.Specs.Chronology

   type step_g (region_t: Type) (state_t: Type) (step_kind_t: Type)
      = region_t 
         -> state_t
         -> step_kind_t 
         -> Tot (state_t * (Seq.seq_g (region_t * step_kind_t)))

   type effect_g (region_t: Type) (state_t: Type) (step_kind_t: Type) =
      | Spawn: 
         region: region_t 
         -> state0: state_t
         -> step: step_g region_t state_t step_kind_t
         -> effect_g region_t state_t step_kind_t
      | Step: 
         region: region_t 
         -> step_kind: step_kind_t 
         -> effect_g region_t state_t step_kind_t

   type _chronology_g (region_t: Type) (state_t: Type) (step_kind_t: Type) =
      {
         log: Seq.seq_g (effect_g region_t state_t step_kind_t);
         spawned: Set.set_g region_t
      }

   type is_chronology_safe: 
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> _chronology_g region_t state_t step_kind_t 
      -> Type
      = 
         fun 
            (region_t: Type) 
            (state_t: Type) 
            (step_kind_t: Type) 
            (_chronology: 
               _chronology_g region_t state_t step_kind_t) 
         ->
            // each region may only be spawned once.
            (forall (region: region_t).
               Set.is_mem _chronology.spawned region ==> 
                  1 =
                     Seq.foldl
                        (fun accum event ->
                           match event with
                              | Spawn region _ _ ->
                                 accum + 1
                              | _ ->
                                 accum)
                        0
                        _chronology.log)
            // all actor ids must be in the set of known ids.
            /\ (forall n.
                  0 <= n && n < Seq.length _chronology.log && is_Spawn (Seq.nth _chronology.log n)
                  ==>
                     Set.is_mem _chronology.spawned (Spawn.region (Seq.nth _chronology.log n)))

   type chronology_g (region_t: Type) (state_t: Type) (step_kind_t: Type) 
      = _chronology: _chronology_g region_t state_t step_kind_t{is_chronology_safe _chronology}

   val init:
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> Tot (chronology_g region_t state_t step_kind_t)
   let init 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      = 
         {
            log = Seq.empty;
            spawned = Set.empty
         }

   val is_spawned:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> chronology_g region_t state_t step_kind_t
      -> region_t
      -> Tot bool
   let is_spawned (region_t: Type) (step_kind_t: Type) chronology region
      = Set.is_mem chronology.spawned region

   val region_log:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> chronology: chronology_g region_t state_t step_kind_t
      -> region: region_t{is_spawned chronology region}
      -> Tot (Seq.seq_g (effect_g region_t state_t step_kind_t))
   let region_log 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      chronology 
      region
      = Seq.filter
            (fun event ->
               match event with
                  | Spawn r _ _ ->
                     r = region
                  | Step r _ ->
                     r = region)
            chronology.log

   val global_log:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> chronology_g region_t state_t step_kind_t
      -> Tot (Seq.seq_g (effect_g region_t state_t step_kind_t))
   let global_log 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      chronology
      = chronology.log

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
