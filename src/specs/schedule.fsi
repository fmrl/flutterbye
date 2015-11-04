(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi FStar.OrdSet;
   other-files:seq.fsi ordset.fsi
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

module Monarch.Specs.Schedule

   type RegionId: Type

   val cmp_region_ids: f:(RegionId -> RegionId -> Tot bool){FStar.OrdSet.total_order RegionId f}

   type Domain = FStar.OrdSet.ordset RegionId cmp_region_ids

   type Effect 'arg 'state =
      | Spawn:(region_id:RegionId -> state0:'state -> Effect 'arg 'state)
      | Cast:(region_id:RegionId -> arg:'arg -> Effect 'arg 'state)

   type Reaction 'arg 'state =
      Effect 'arg 'state
      -> 'state
      -> Tot ((FStar.Seq.seq (Effect 'arg 'state)) * 'state)
                        // (consequential effects * new state)

   type Schedule: Type -> Type -> Type

   val empty:
      Reaction 'arg 'state
      -> 'state
      -> Tot (Schedule 'arg 'state)

   val length: Schedule 'arg 'state -> Tot nat

   val domain: Schedule 'arg 'state -> Tot OrdRegionIdSet

   val event:
      scd:Schedule 'arg 'state
      -> ord:nat{ord < length scd}
      -> Tot (Effect 'arg 'state)

   val state:
      scd:Schedule 'arg 'state
      -> ord:nat{ord < length scd}
      -> Tot 'state

   (*val filter:
      scd:Schedule 'arg 'state
      -> rid:nat{rid < width scd}
      -> Tot (Schedule 'arg 'state)*)

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
