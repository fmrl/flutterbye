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

   val mem: seq 'a -> 'a -> Tot bool

   val lemma__basic:
      s: seq 'a
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures
            ((mem s a)
               <==>
                  (exists i.
                     0 <= i
                     && i < length s
                     && index s i = a)))
         [SMTPat (mem s a)]

   val lemma__slice:
      s0: seq 'a
      -> a: 'a
      -> s1: seq 'a
      -> j: nat{j <= length s1}
      -> i: nat{0 <= i && i <= j}
      -> Lemma
         (requires (mem s0 a))
         (ensures (Eq s0 (slice s1 i j) ==> mem s1 a))
         [SMTPat (mem (slice s1 i j) a)]

   val lemma__index:
      s:seq 'a{length s > 0}
      -> i:nat{i < length s}
      -> Lemma
         (requires (True))
         (ensures (mem s (index s i)))
         [SMTPat (mem s (index s i))]

   val lemma__append:
      s0: seq 'a
      -> s1: seq 'a
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (mem s0 a || mem s1 a <==> mem (append s0 s1) a))
         [SMTPat (mem (append s0 s1) a)]
