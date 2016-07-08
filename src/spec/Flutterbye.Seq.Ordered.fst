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

val tmp_lemma:
   lte:compare_t 'a{partial_order_p lte} ->
   s:seq 'a{ordered_p lte s} ->
   a: 'a ->
   Lemma
      (ensures 
            (forall (x:nat{x < length s}). lte (index s x) a))
let tmp_lemma lte s a =
   admit ()

abstract val append_lemma_loop:
   lte:compare_t 'a{partial_order_p lte} ->
   s:seq 'a{ordered_p lte s} ->
   a: 'a ->
   Lemma
      (requires (length s = 0 || lte (index s (length s - 1)) a))
      (ensures (ordered_p lte (append s (create 1 a))))
let append_lemma_loop lte s a =
   if length s > 1 then
      begin
         tmp_lemma lte s a;
         ()
      end
   else
      ()

      (*
abstract val append_lemma:
   lte:compare_t 'a{partial_order_p lte} ->
   s_1:seq 'a{ordered_p lte s_1} ->
   s_2:seq 'a{ordered_p lte s_2} ->
   Lemma
      (*(requires (
         // either `s_1` or `s_2` are of zero length
         length s_1 = 0 || length s_2 = 0
         // or the first element of `s_2` must not be less than the final element of `s_1`.
         || lte (index s_1 (length s_1 - 1)) (index s_2 0)
      ))*)
      (ensures (ordered_p lte (append s_1 s_2)))
let append_lemma lte s_1 s_2 =
   if length s_1 > 0 && length s_2 > 0 then
      begin
         let s' = append s_1 s_2 in
         assert
            (forall (x:nat{x < length s_1}) (y:nat{y < length s_1}).
               ((x <= y) <==> (lte (index s' x) (index s' y))));
         assert
            (forall (x:nat{x < length s_2}) (y:nat{y < length s_2}).
               ((x <= y) <==> (lte (index s' (x + length s_1)) (index s' (y + length s_1)))));
         assert (length s' = length s_1 + length s_2);
         assert (length s_1 - 1 >= 0);
         assert (lte (index s' (length s_1 - 1)) (index s' (length s_1)));
         assert
            (forall (x:nat{x <= length s_1}) (y:nat{y <= length s_1}).
               ((x <= y) <==> (lte (index s' x) (index s' y))));
         assert
            (forall (x:nat{x < length s'}) (y:nat{y < length s'}).
               ((x <= y) <==> (lte (index s' x) (index s' y))));
         admit ()
      end
   else
      ()*)

      (*(requires (
         // either `s_1` or `s_2` are of zero length
         length s_1 = 0 || length s_2 = 0
         // or the first element of `s_2` must not be less than the final element of `s_1`.
         || lte (index s_1 (length s_1 - 1)) (index s_2 0)
      ))*)
