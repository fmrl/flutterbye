// $legal:629:
//
// Copyright 2016 Michael Lowell Roberts & Microsoft Research
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
//,$

module Flutterbye.Seq.Temporal
open FStar.Seq

let next_p (#a_t:Type) (s:seq a_t) (p:(a_t -> Type)) = 
   length s > 1 /\ p (index s 1)

let future_p (#a_t:Type) (s:seq a_t) (p:(a_t -> Type)) =
   length s > 1 
   /\ (exists (x:nat{x < length s}).
         x > 0 /\ p (index s x))

let global_p (#a_t:Type) (s:seq a_t) (p:(a_t -> Type)) =
   length s > 1 
   /\ (forall (x:nat{x < length s}).
         x > 0 ==> p (index s x))
