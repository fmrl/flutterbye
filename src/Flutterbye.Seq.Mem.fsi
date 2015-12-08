(*--build-config
   options:--admit_fsi FStar.Seq;
   other-files:seq.fsi
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

module Flutterbye.Seq.Mem
open FStar.Seq

type Mem (#a:Type) (x:a) (s:seq a) =
   exists (i:nat).
      i < length s && index s i = x

val mem: x:'a -> s:seq 'a -> Tot (b:bool{b <==> Mem x s})

val lemma__slice_1:
   a:'a
   -> s:seq 'a
   -> Lemma
      (requires (mem a s))
      (ensures
         (forall (i:nat) (j:nat) (q:seq 'a).
            ((j < length q /\ i <= j /\ (Eq s (slice q i j))) ==>
               mem a q)))

// todo: this lemma could be generalized to any slice containing index `i`.
// (would that subsume lemma__slice_1?)
val lemma__slice_2:
   a:'a
   -> s:seq 'a
   -> Lemma
      (requires (mem a s))
      (ensures
         (forall (i:nat).
            ((i < length s && index s i = a) ==>
               (mem a (slice s 0 (i + 1))))))

val lemma__index:
   s:seq 'a{length s > 0}
   -> i:nat{i < length s}
   -> Lemma
      (requires (True))
      (ensures (mem (index s i) s))

val lemma__append:
   x:'a
   -> s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires (mem x s_1 || mem x s_2))
      (ensures (mem x (append s_1 s_2)))

val lemma__empty:
   x:'a
   -> s:seq 'a
   -> Lemma
      (requires (length s = 0))
      (ensures (not (mem x s)))
      [SMTPat (mem x s)]

val lemma__create:
   n:nat{n > 0}
   -> a:'a
   -> Lemma
      (requires (True))
      (ensures (mem a (create n a)))
      [SMTPat (create n a)]
