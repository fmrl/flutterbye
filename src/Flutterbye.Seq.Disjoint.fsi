(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi Flutterbye.Seq.Mem --admit_fsi Flutterbye.Seq.Unique;
   other-files:seq.fsi set.fsi Flutterbye.Seq.Mem.fsi Flutterbye.Seq.Unique.fsi
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
// limitations under the Licenses
//
// ,$

module Flutterbye.Seq.Disjoint
open FStar.Seq
open FStar.Set
open Flutterbye.Seq.Unique

type Disjoint: #a:Type -> s_1:seq a -> s_2:seq a -> Type

val lemma__intersect:
   s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires
         (Equal
            empty
            (intersect
               (to_set (unique s_1))
               (to_set (unique s_2)))))
      (ensures (Disjoint s_1 s_2))

val lemma__mem:
   x:'a
   -> s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires (Disjoint s_1 s_2))
      (ensures
         ((Flutterbye.Seq.Mem.mem x s_1 \/ Flutterbye.Seq.Mem.mem x s_2) <==>
            ((Flutterbye.Seq.Mem.mem x s_1 <==>
               not (Flutterbye.Seq.Mem.mem x s_2)))))
