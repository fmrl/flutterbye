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

val mem: 'a -> seq 'a -> Tot bool

val lemma__mem:
   a:'a
   -> s:seq 'a
   -> Lemma
      (requires (True))
      (ensures
         ((mem a s)
            <==>
               (exists i.
                  0 <= i
                  && i < length s
                  && index s i = a)))
      [SMTPat (mem a s)]

val lemma__slice:
   s:seq 'a
   -> a:'a
   -> Lemma
      (requires (mem a s))
      (ensures
         ((forall (i:nat) (j:nat) (s1:seq 'a).
            ((j < length s1 /\ i <= j /\ (Eq s (slice s1 i j))) ==>
               mem a s1)))
         /\
            (forall (i:nat).
               ((i < length s && index s i = a) ==>
                  (mem a (slice s 0 (i + 1))))))

val lemma__index:
   s:seq 'a{length s > 0}
   -> i:nat{i < length s}
   -> Lemma
      (requires (True))
      (ensures (mem (index s i) s))
      [SMTPat (mem (index s i) s)]

val lemma__append:
   a:'a
   -> s0:seq 'a
   -> s1:seq 'a
   -> Lemma
      (requires (True))
      (ensures ((mem a s0 || mem a s1) <==> (mem a (append s0 s1))))
