(*--build-config
   options:--admit_fsi Seq;
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

module Tesseract.Specs.SeqExt
   open Seq

   val mem: seq 'a -> 'a -> Tot bool

   val lemma_mem__mem:
      s: seq 'a
      -> a: 'a
      -> Lemma
         (requires True)
         (ensures
            ((mem s a)
               ==>
                  (exists i.
                     (0 <= i && i < length s)
                     ==>
                        (index s i = a))))
         [SMTPat (mem s a)]

   val filter:
      // predicate; if false, then the element is discarded from the sequence.
      ('a -> Tot bool)
      // input sequence
      -> seq 'a
      // output sequence
      -> Tot (seq 'a)

   val lemma_filter__length:
      p: ('a -> Tot bool) ->
      s: seq 'a ->
      Lemma
         (requires True)
         (ensures (length (filter p s) <= length s))
         [SMTPat (length (filter p s))]

   val lemma_filter__admission:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> i: nat{i < length (filter p s)}
      -> Lemma
         (requires True)
         (ensures (p (index (filter p s) i)))
         [SMTPat (index (filter p s) i)]

   val insert:
      s: seq 'a
      -> i: nat{i <= length s}
      -> 'a
      -> Tot (seq 'a)

   val lemma_insert__length:
      s: seq 'a
      -> i: nat{i <= length s}
      -> a: 'a
      -> Lemma
         (requires True)
         (ensures (length (insert s i a) = length s + 1))
         [SMTPat (length (insert s i a))]

   val lemma_insert__contents:
      s: seq 'a
      -> i: nat{i <= length s}
      -> a: 'a
      -> Lemma
         (ensures
            (index (insert s i a) i = a
            /\ (forall j. 0 <= j && j < i
               ==> index (insert s i a) j = index s j)
            /\ (forall j. i < j && j < length (insert s i a)
               ==> index (insert s i a) j = index s (j - 1))))

   val remove:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> 'a
      -> Tot (seq 'a)

   val lemma_remove__length:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> a: 'a
      -> Lemma
         (requires True)
         (ensures (length (remove s i a) = length s - 1))
         [SMTPat (length (remove s i a))]

   val lemma_remove__contents:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> a: 'a
      -> Lemma
         (ensures
            ((forall j. 0 <= j && j < i
               ==> index (remove s i a) j = index s j)
            /\ (forall j. i <= j && j < length (remove s i a)
               ==> index (remove s i a) j = index s (j + 1))))
