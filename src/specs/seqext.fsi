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

   val map:
      // high-order mapping function
      ('a -> Tot 'b)
      // input sequence
      -> s: seq 'a
      // output sequence
      -> Tot (seq 'b)

   val mem: seq 'a -> 'a -> Tot bool

   val filter:
      ('a -> Tot bool)
         // predicate; if false, then the element is discarded from the
         // sequence.
      -> seq 'a // input sequence
      -> Tot (seq 'a) // output sequence

   val insert:
      s: seq 'a
      -> i: nat{i <= length s}
      -> 'a
      -> Tot (seq 'a)

   val remove:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> 'a
      -> Tot (seq 'a)

   // lemmas

   val lemma_map__length:
      f: ('a -> Tot 'b)
      -> s: seq 'a
      -> Lemma
         (requires (True))
         (ensures (length (map f s) = length s))
         [SMTPat (length (map f s))]

   val lemma_map__map:
      f: ('a -> Tot 'b)
      -> s: seq 'a
      -> i: nat{i < length s}
      -> Lemma
         (requires (True))
         (ensures (index (map f s) i = f (index s i)))
         [SMTPat (index (map f s) i)]

   val lemma_mem__index:
      s:seq 'a{length s > 0}
      -> i:nat{i < length s}
      -> Lemma
         (requires (True))
         (ensures (mem s (index s i)))
         [SMTPat (mem s (index s i))]

   val lemma_filter__length:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> Lemma
         (requires (True))
         (ensures (length (filter p s) <= length s))
         [SMTPat (length (filter p s))]

   val lemma_filter__admission:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> i: nat{i < length (filter p s)}
      -> Lemma
         (requires (True))
         (ensures (p (index (filter p s) i)))
         [SMTPat (index (filter p s) i)]

   val lemma_insert__length:
      s: seq 'a
      -> i: nat{i <= length s}
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (length (insert s i a) = length s + 1))
         [SMTPat (length (insert s i a))]

   val lemma_insert__contents:
      s: seq 'a
      -> i: nat{i <= length s}
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures
            (index (insert s i a) i = a
            /\ (forall j. 0 <= j && j < i
               ==> index (insert s i a) j = index s j)
            /\ (forall j. i < j && j < length (insert s i a)
               ==> index (insert s i a) j = index s (j - 1))))
         // todo: need trigger.

   val lemma_remove__length:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (length (remove s i a) = length s - 1))
         [SMTPat (length (remove s i a))]

   val lemma_remove__contents:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures
            ((forall j. 0 <= j && j < i
               ==> index (remove s i a) j = index s j)
            /\ (forall j. i <= j && j < length (remove s i a)
               ==> index (remove s i a) j = index s (j + 1))))
         // todo: need trigger
