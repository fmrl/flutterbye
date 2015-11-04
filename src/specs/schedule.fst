(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi FStar.OrdSet --admit_fsi Monarch.Specs.SeqExt;
   other-files:seq.fsi ordset.fsi schedule.fsi alt/option.fst seqext.fsi
--*)

module Monarch.Specs.Schedule

   type RegionId = nat

   // [bug][fstar] apparently, i shouldn't need to re-specify the following type.
   // [bug][fstar] verbatium re-specification of the following type causes a
   // compiler error.
   val cmp_region_ids: RegionId -> RegionId -> Tot bool
   let cmp_region_ids lhs rhs = (lhs <= rhs)

   type Effect 'arg 'state =
      | Spawn:(region_id:RegionId -> state0:'state -> Effect 'arg 'state)
      | Stimulate:(region_id:RegionId -> arg:'arg -> Effect 'arg 'state)

   type Reaction (arg:Type) (state:Type) =
      Effect arg state
      -> state
      -> Tot ((FStar.Seq.seq (Effect arg state)) * state)

   type Schedule 'arg 'state =
      | MkSched:
         react:Reaction 'arg 'state
         -> events:(FStar.Seq.seq (Effect 'arg 'state))
         -> Schedule 'arg 'state

   let empty react state0 =
      MkSched react (FStar.Seq.create 1 (Spawn 0 state0))

   let length sched =
      FStar.Seq.length (MkSched.events sched)

   val domain: Schedule 'arg 'state -> Tot Domain
   let domain sched =
      let d =
         SeqExt map
            (fun ef ->
               match ef with
                  | Spawn r _ ->
                     r
                  | Stimulate r _ ->
                     r)
            (MkSched.events sched) in
      let d' =



   val filter:
      scd:Schedule 'arg 'state
      -> rid:nat{rid < width scd}
      -> Tot (Schedule 'arg 'state)

   let event cron idx =

   val state:
      scd:Schedule 'arg 'state
      -> idx:nat{idx < length scd}
      -> Tot 'state


   ///

   (*type Schedule 'arg 'state =
      | MkSched:
         react:(Reaction 'arg 'state)
         -> state0:'state
         -> log:(seq (Effect 'arg 'state))
         -> Schedule 'arg 'state*)

   type _Chronology 'arg 'state =
      | MkSched:
         react:(Reaction 'arg 'state)
         -> state0:'state
         -> log:(seq (Effect 'arg 'state))
         -> _Chronology 'arg 'state
   type Schedule =
      fun (arg:Type) (state:Type) ->
         _Chronology arg state



   let event cron i =
      index (Schedule.log cron) i

   val __state__build: Schedule 'arg 'state -> nat -> nat -> 'state
   let rec __state__build cron regid idx' idx accum =
      let e = index cron idx in
      match e with
         | Spawn (r:nat{r = regid}) s0 ->
            assert (is_None accum);
            Some s0
         | _ ->
            accum




   let state cron region_id i =
      __state__build region_id i 0 None

(*type ChronologyInvariant__region_id_order:
      #arg:Type
      -> #state:Type
      -> cron: ChronologyStruct arg state
      -> Type =
   fun 'arg 'state cron ->
      0 = length cron.log
      \/ (forall i j.
            0 < i
            && i < length (cron.log)
            && Spawn = (index cron.log i).evt.eff.knd
            && 0 <= j
            && j < i
            ==>
               (index cron.log j).evt.eff.rid < (index cron.log i).evt.eff.rid)

type ChronologyInvariant:
      #arg:Type
      -> #state:Type
      -> cron: ChronologyStruct arg state
      -> Type =
   fun 'arg 'state cron ->
      ChronologyInvariant__region_id_order cron*)
