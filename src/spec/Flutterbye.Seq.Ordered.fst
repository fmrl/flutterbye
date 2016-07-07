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
   length s < 2
   \/ (forall (x:nat{x < length s}) (y:nat{y < length s}).
         ((x <= y) <==> (lte (index s x) (index s y))))

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

abstract val append_lemma:
   lte:compare_t 'a{partial_order_p lte} ->
   s_1:seq 'a{ordered_p lte s_1} ->
   s_2:seq 'a{ordered_p lte s_2} ->
   Lemma
      (ensures (ordered_p lte (append s_1 s_2)))
let append_lemma lte s_1 s_2 =
   if length s_1 > 0 && length s_2 > 0 then
      admit ()
   else
      ()

      (*(requires (
         // either `s_1` or `s_2` are of zero length
         length s_1 = 0 || length s_2 = 0
         // or the first element of `s_2` must not be less than the final element of `s_1`.
         || lte (index s_1 (length s_1 - 1)) (index s_2 0)
      ))*)
