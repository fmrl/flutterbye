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

module Flutterbye.Seq.Contains
open FStar.Seq
open Flutterbye.Option
open Flutterbye.Seq.Find
open Flutterbye.Seq.Remove

type contains_p (#a_t:Type) (f:a_t -> Tot bool) (s:seq a_t) =
   exists (x:nat{x < length s}).
      f (index s x)

val contains:
      f:('a -> Tot bool)
   -> s:seq 'a
   -> Tot (b:bool{b2t b <==> contains_p f s})
let contains f s =
   is_Some (find f s)

abstract val index_lemma:
      s:seq 'a
   -> Lemma
      (ensures
         // if an element obtained from the sequence satisfies `f` then
         // `contains_p f s` is true.
         (length s > 0 ==>
            (forall (f:'a -> Tot bool) (x:nat{x < length s}).
               f (index s x) ==> contains_p f s)))
let index_lemma s =
   ()

abstract val slice_lemma:
      s:seq 'a
   -> Lemma
      (ensures
         (forall (f:'a -> Tot bool) (x:nat) (y:nat).
            // if [x, y) describes a non-empty (where x < y) slice of `s`...
            (y <= length s /\ x < y) ==>
               // then any slice that satisfies `f` means `s` is satisfied.
               contains_p f (slice s x y) ==> contains_p f s))
let slice_lemma s =
   ()

private type empty_p (#a_t:Type) (s:seq a_t) =
   forall (f:a_t -> Tot bool).
      ~ (contains_p f s)

// this function is used as a witness
private val eq: 'a -> 'a -> Tot bool
let eq a_1 a_2 =
   a_1 = a_2

abstract val empty_lemma:
      s:seq 'a
   -> Lemma (ensures (length s = 0 <==> empty_p s))
let empty_lemma s =
   Flutterbye.Seq.Find.empty_lemma s

abstract val create_lemma:
      n:nat
   -> a:'a
   -> Lemma
      (ensures
         (  // if we are creating an empty sequence, then the empty rule applies.
            (n = 0 <==> (forall (f:'a -> Tot bool). empty_p (create n a)))
         /\ // otherwise, `f a` is the identical to `contains_p f s`.
            (n > 0 ==> (forall (f:'a -> Tot bool). (f a <==> contains_p f (create n a))))))
let create_lemma n a =
   Flutterbye.Seq.Find.create_lemma n a

abstract val append_lemma:
      s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (ensures
         (  // if the first sequence satisfies the predicate, the "appended" sequence
            // will also.
            (forall (f:'a -> Tot bool).
               (contains_p f s_1 ==> contains_p f (append s_1 s_2)))
         /\ // if the second sequence satisfies the predicate, the "appended" sequence
            // will also.
            (forall (f:'a -> Tot bool).
               (contains_p f s_2 ==> contains_p f (append s_1 s_2)))
         /\ // if one of the two input sequences satisfies the predivate, the "appended"
            // sequence will also, and vice versa.
            (forall (f:'a -> Tot bool).
               (contains_p f (append s_1 s_2) <==> (contains_p f s_1 \/ contains_p f s_2)))
         )
      )
let append_lemma s_1 s_2 =
   Flutterbye.Seq.Find.append_lemma s_1 s_2

val remove_lemma:
      s:seq 'a{length s > 0}
   -> i:nat{i < length s}
   -> f:('a -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures
         (  // if the input sequence doesn't have an element that satisfies
            // `f` then the output won't either.
            (~ (contains_p f s) ==> ~ (contains_p f (remove s i)))

            // if an element in the input sequence that satisfies `f` can be
            // found and that element is not being removed from the sequence,
            // the output sequence will also satisfy `f`.
         /\ ((contains_p f s /\ get (find f s) <> i) ==> contains_p f (remove s i))
         )
      )
let remove_lemma s i f =
   Flutterbye.Seq.Find.remove_lemma s i f
