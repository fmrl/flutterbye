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

   type _chronology_g 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      = Seq.seq_g (effect_g region_t state_t step_kind_t)

   val is_spawn_effect_for: 
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type
      -> region_t
      -> effect_g region_t state_t step_kind_t
      -> Tot bool
   let is_spawn_effect_for 
      (region_t: Type) 
      (state_t: Type)
      (step_kind_t: Type)
      region
      ffct
      = (is_Spawn ffct)
         && (region = Spawn.region ffct)

   type is_chronology_safe: 
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> _chronology_g region_t state_t step_kind_t 
      -> Type
      = fun 
         (region_t: Type) 
         (state_t: Type) 
         (step_kind_t: Type) 
         (cron: 
            _chronology_g region_t state_t step_kind_t) 
         -> // an empty chronology is safe (though useless).
            (0 = Seq.length cron)
            \/ // forall Spawn effect kinds in the sequence...
               (forall (n: nat).
                  (n < Seq.length cron)
                  && (is_Spawn (Seq.nth cron n))
                  ==>
                     (1 == Seq.length cron)
                     \/ // no other spawn effect kind is permitted
                        // in the same chronology for a given region.
                        ((let seq' = Seq.remove cron n in
                        let region = Spawn.region (Seq.nth cron n) in
                        is_None (Seq.maybe_find (is_spawn_effect_for region) seq' 0))
                        // regions may not react to step effects
                        // until after their singular spawn effect.
                        /\ (forall (i: nat).
                              (i < n)
                              && (is_Step (Seq.nth cron n))
                              ==> 
                                 (let ffct = Seq.nth cron n in 
                                 let ffct' = Seq.nth cron i in
                                 (Spawn.region ffct) 
                                 <> (Spawn.region ffct')))))

   type chronology_g 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      = cron: 
         _chronology_g 
            region_t 
            state_t 
            step_kind_t{is_chronology_safe cron}

   val init:
      #region_t: Type 
      -> #state_t: Type 
      -> #step_kind_t: Type 
      -> Tot (chronology_g region_t state_t step_kind_t)
   let init 
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      = Seq.empty

   val is_spawned:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> chronology_g region_t state_t step_kind_t
      -> region_t
      -> Tot bool
   let is_spawned 
      (region_t: Type) 
      (step_kind_t: Type) 
      chronology 
      region
      = if 0 = Seq.length chronology then
            false
         else
            is_Some (Seq.maybe_find is_Spawn chronology 0)

   val filter_by_region:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> chronology: chronology_g region_t state_t step_kind_t
      -> region: region_t{is_spawned chronology region}
      -> Tot (Seq.seq_g (effect_g region_t state_t step_kind_t))
   let filter_by_region 
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
            chronology

   (*val spawn:
      #region_t: Type
      -> #state_t: Type
      -> #step_kind_t: Type
      -> cron: chronology_g region_t state_t step_kind_t
      -> region: region_t{not (is_spawned cron region)}
      -> state_t
      -> step_g region_t state_t step_kind_t
      -> Tot (chronology_g region_t state_t step_kind_t)
   let spawn
      (region_t: Type) 
      (state_t: Type) 
      (step_kind_t: Type) 
      cron 
      region
      state0
      step
      = Seq.append cron (Spawn region state0 step)*)

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
