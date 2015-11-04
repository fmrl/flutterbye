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

module Flutterbye.Specs.SeqExt
   open FStar.Seq

   // todo: this isn't working when used from Alt.Option
   val option_get: o: option 'a{is_Some o} -> Tot 'a

   val find: s: seq 'a -> 'a -> Tot (option nat)

   val mem: seq 'a -> 'a -> Tot bool

   val filter:
      ('a -> Tot bool)
         // predicate; if false, then the element is discarded from the
         // sequence.
      -> seq 'a // input sequence
      -> Tot (seq 'a) // output sequence

   val count:
      ('a -> Tot bool)
         // predicate; if false, then the element is discarded from the
         // sequence.
      -> seq 'a // input sequence
      -> Tot nat

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

   type IsSet: #a:Type -> s:seq a -> Type

   val is_set: (s:seq 'a) -> Tot bool

   // lemmas

   val lemma_find__index:
      s: seq 'a
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures
            ((is_None (find s a) ==>
               (forall j.
                  0 <= j && j < length s ==> index s j <> a))
            /\ (is_Some (find s a) ==>
                  ((option_get (find s a)) < length s
                  && a = index s (option_get (find s a))))))
         [SMTPat (find s a)]

   val lemma_mem__mem:
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

   val lemma_mem__slice:
      s0: seq 'a
      -> a: 'a
      -> s1: seq 'a
      -> j: nat{j <= length s1}
      -> i: nat{i <= j}
      -> Lemma
         (requires (mem s0 a))
         (ensures (Eq s0 (slice s1 i j) ==> mem s1 a))
         [SMTPat (mem (slice s1 i j) a)]

   val lemma_mem__index:
      s:seq 'a{length s > 0}
      -> i:nat{i < length s}
      -> Lemma
         (requires (True))
         (ensures (mem s (index s i)))
         [SMTPat (mem s (index s i))]

   // todo: breaks f* if moved to seqext.fsi.
   val lemma_mem__slice:
      s0: seq 'a
      -> a: 'a
      -> s1: seq 'a
      -> j: nat{j <= length s1}
      -> i: nat{0 <= i && i <= j}
      -> Lemma
         (requires (mem s0 a))
         (ensures (Eq s0 (slice s1 i j) ==> mem s1 a))
         [SMTPat (mem (slice s1 i j) a)]

   val lemma_mem__append:
      s0: seq 'a
      -> s1: seq 'a
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (mem s0 a || mem s1 a <==> mem (append s0 s1) a))
         [SMTPat (mem (append s0 s1) a)]

   val lemma_filter__admission:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> i: nat{i < length (filter p s)}
      -> Lemma
         (requires (True))
         (ensures (p (index (filter p s) i)))
         [SMTPat (index (filter p s) i)]

   val lemma_filter__mem:
      p: ('a -> Tot bool) ->
      s: seq 'a ->
      Lemma
         (requires (True))
         (ensures
            (forall i.
               0 <= i && i < length (filter p s)
               ==> mem s (index (filter p s) i)))

   val lemma_count__length:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> Lemma
         (requires (True))
         (ensures (count p s <= length s))
         [SMTPat (count p s)]

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

   val lemma_is_set__is_set:
      s:seq 'a
      -> Lemma
         (requires (True))
         (ensures (is_set s <==> IsSet s))
