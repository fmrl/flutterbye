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

module Flutterbye.Seq.Filter
open FStar.Seq
open Flutterbye.Seq.Mem

// todo: maintain ordering.
// todo: maintain counts for elements that satisfy `f`.
type filtered_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (s':seq a_t) =
   // if the input sequence is empty, then the output sequence will also be.
   (length s = 0 ==> length s' = 0) /\
   // if the input sequence is not empty...
   (length s > 0 ==>
      // then the input sequence won't be smaller than the output sequence.
      (length s >= length s' /\
         // if the output sequence is empty, then the no element of `s` satisfies `f`.
         (length s' = 0 ==>
            (forall (x:nat).
               x < length s ==> not (f (index s x))) /\
         // if the output sequence is not empty...
         (length s' > 0 ==>
            // then every element of `s'`...
            (forall (x:nat).
               x < length s' ==>
                  // satisfies `f`.
                  (f (index s' x) &&
                  // and is a member of `s`.
                  mem (index s' x) s))))))

private val filter_loop:
   f:('a -> Tot bool) ->
   s:seq 'a ->
   i:nat{i <= length s} ->
   ac:seq 'a ->
   Tot (ac':seq 'a)
      (decreases (length s - i))
let rec filter_loop f s i ac =
   if i < length s then
      let a = index s i in
      let ac' =
         if f a then
            append ac (create 1 a)
         else
            ac in
      filter_loop f s (i + 1) ac'
   else
      ac

private val filter_loop_lemma:
   f:('a -> Tot bool) ->
   s:seq 'a ->
   i:nat{i <= length s} ->
   ac:seq 'a ->
   Lemma
      (requires (filtered_p f (slice s 0 i) ac))
      (ensures (filtered_p f s (filter_loop f s i ac)))
      (decreases (length s - i))
let rec filter_loop_lemma f s i ac =
   slice_lemma s;
   if i < length s then
      let a = index s i in
      let ac' =
         if f a then
            append ac (create 1 a)
         else
            ac in
      filter_loop_lemma f s (i + 1) ac'
   else
      ()

val filter:
   f:('a -> Tot bool) ->
   s:seq 'a ->
   Tot (s':seq 'a{filtered_p f s s'})
let filter f s =
   filter_loop_lemma f s 0 createEmpty;
   filter_loop f s 0 createEmpty
