(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi Flutterbye.Seq.Mem;
   other-files:seq.fsi set.fsi Flutterbye.Seq.Mem.fsi
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

module Flutterbye.Seq.Unique
open FStar.Seq
open FStar.Set

type Unique: #a:Type -> s:seq a -> Type

val unique: (s:seq 'a) -> Tot bool
val to_set: (s:seq 'a{Unique s}) -> Tot (set 'a)

val lemma__reveal:
   s:seq 'a
   -> Lemma
      (requires (Unique s))
      (ensures
         (0 = length s
         \/ (forall (i:nat) (j:nat).
               i < length s
               && j < length s
               && index s j = index s i
               ==>
                  j == i)))

val lemma__unique:
   s:seq 'a
   -> Lemma
      (requires (True))
      (ensures (unique s <==> Unique s))
      // todo: need pattern

val lemma__empty: s:seq 'a -> Lemma
   (requires (True))
   (ensures (Eq createEmpty s ==> Unique s))
   // todo: need pattern

val lemma__to_set:
   (s:seq 'a{Unique s})
   -> Lemma
      (requires (True))
      (ensures
         (forall a.
            Flutterbye.Seq.Mem.mem a s <==> mem a (to_set s)))
