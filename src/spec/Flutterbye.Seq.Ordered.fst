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

module Flutterbye.Seq.Ordered
open FStar.Seq
open Flutterbye.Order

type ordered_p (#a_t:Type) (lte:compare_t a_t{partial_order_p lte}) (s:seq a_t) =
   length s = 0
   \/ (forall (x:nat{x < length s}) (y:nat{y < length s}).
         (x <= y) ==> lte (index s x) (index s y))

abstract val slice_lemma:
   lte:compare_t 'a{partial_order_p lte} ->
   s:seq 'a{ordered_p lte s} ->
   Lemma
      (ensures
         // if [x, y) describe a slice of `s`, then that slice is also partially ordered.
         (forall (x:nat) (y:nat{y < length s}).
            x <= y ==> ordered_p lte (slice s x y)))
let slice_lemma lte s =
   ()

private val append_lemma_loop:
   lte:compare_t 'a{partial_order_p lte} ->
   s:seq 'a{ordered_p lte s} ->
   a: 'a ->
   i:nat{0 < i && i <= length s} ->
   Lemma
      (requires 
        (forall (x:nat{x < length s}). 
            x >= length s - i ==> lte (index s x) a))
      (ensures (forall (x:nat{x < length s}). lte (index s x) a))
      (decreases (length s - i))
let rec append_lemma_loop lte s a i =
   if i < length s then
      let a_i = index s (length s - 1 - i) in
      // both of the following assertions are necessary to
      // estabilsh the transitivity of a_i <= a_last <= a.
      assert (lte a_i (index s (length s - 1)));
      assert (lte a_i a);
      append_lemma_loop lte s a (i + 1)
   else
      ()

abstract val append_lemma:
   lte:compare_t 'a{partial_order_p lte} ->
   s:seq 'a{ordered_p lte s} ->
   a: 'a ->
   Lemma
      (requires (length s = 0 || lte (index s (length s - 1)) a))
      (ensures (ordered_p lte (append s (create 1 a))))
let append_lemma lte s a =
   if length s = 0 then
      ()
   else
      append_lemma_loop lte s a 1

