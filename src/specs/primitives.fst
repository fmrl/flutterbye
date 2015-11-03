(*--build-config
   options:--admit_fsi Seq;
   other-files:seq.fsi primitives.fsi
--*)

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

module Flutterbye.Specs.Primitives
   open Seq

   type Chronology 'arg 'state =
      | MkCron:
         react:(Reaction 'arg 'state)
         -> state0:'state
         -> log:(seq (Effect 'arg 'state))
         -> Chronology 'arg 'state

   let empty react state0 arg =
      let effect0 = {
         region_id = 0;
         effect_kind = Spawn;
         arg = arg
      } in
      MkCron react state0 (create 1 effect0)

   let length cron =
      length (Chronology.log cron)

   let event cron i =
      index (Chronology.log cron) i

   let first cron =
      let evt = index cron 0 in
      assert (evt.effect_kind = Spawn);
      evt.region_id

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
