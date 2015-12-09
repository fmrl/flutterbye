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

val to_set: (s:seq 'a{Unique s}) -> Tot (set 'a)
val unique: (s:seq 'a) -> Tot (u:seq 'a{Unique u})

val lemma__to_set:
   x:'a
   -> s:seq 'a{Unique s}
   -> Lemma
      (requires (True))
      (ensures (Flutterbye.Seq.Mem.mem x s <==> mem x (to_set s)))

val lemma__empty:
   s:seq 'a
   -> Lemma
      (requires (length s = 0))
      (ensures (Unique s))

val lemma__unique__length:
   s:seq 'a
   -> Lemma
      (requires (True))
      (ensures (length (unique s) <= length s))

// todo: are there disadvantages to combining the two `lemma__unique...` lemmas
// given that one needs an additional free variable?
val lemma__unique__mem:
   x:'a
   -> s:seq 'a
   -> Lemma
      (requires (True))
      (ensures
         (Flutterbye.Seq.Mem.mem x (unique s) <==>
            Flutterbye.Seq.Mem.mem x s))
