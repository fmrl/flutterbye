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
open Flutterbye.Seq.Satisfies

// todo: ordering?
// todo: counting?

// if the input sequence is empty, then the output sequence will also be.
type empty_source_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (s':seq a_t) =
   (length s = 0) ==> (length s' = 0)

// if the input sequence is not empty then the output sequence won't be larger than
// the input sequence.
type not_longer_than_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (s':seq a_t) =
   (length s > 0) ==> (length s >= length s')

// if the output sequence is empty, then the no element of `s` satisfies `f`.
type when_nothing_satisfies_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (s':seq a_t) =
   (length s' = 0) <==> (not (satisfies f s))

// the the output sequence is not empty, then every element must satisfy `f`
type everything_satisfies_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (s':seq a_t) =
   (
       (length s' > 0)
   ==> (forall (x:nat{x < length s'}).
          f (index s' x))
   )

// the the output sequence is not empty, then every element must be a member of `s`.
type shared_membership_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (s':seq a_t) =
   (
       (length s' > 0)
   ==> (forall (x:nat{x < length s'}).
          b2t (mem (index s' x) s))
   )

type filtered_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (s':seq a_t) =
      empty_source_p f s s' 
   /\ not_longer_than_p f s s'
   /\ everything_satisfies_p f s s'
   /\ shared_membership_p f s s'
   /\ when_nothing_satisfies_p f s s'

private val filter_loop:
      f:('a -> Tot bool) 
   -> s:seq 'a 
   -> i:nat{i <= length s} 
   -> ac:seq 'a 
   -> Tot (ac':seq 'a)
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
      f:('a -> Tot bool) 
   -> s:seq 'a 
   -> i:nat{i <= length s} 
   -> ac:seq 'a 
   -> Lemma
      (requires (filtered_p f (slice s 0 i) ac))
      (ensures (filtered_p f s (filter_loop f s i ac)))
      (decreases (length s - i))
let rec filter_loop_lemma f s i ac =
   let sl = slice s 0 i in
   if i < length s then begin
      let sl' = slice s 0 (i + 1) in
      let a = index s i in
      assert (equal sl' (append sl (create 1 a)));
      if f a then
         let ac' = append ac (create 1 a) in
         assert (length ac' > 0);
         assert (b2t (f (index sl' i)));
         assert (satisfies_p f sl');
         assert (when_nothing_satisfies_p f sl' ac');
         filter_loop_lemma f s (i + 1) ac'
      else begin
         assert (when_nothing_satisfies_p f sl ac);
         assert (when_nothing_satisfies_p f sl' ac);
         filter_loop_lemma f s (i + 1) ac
      end
   end
   else begin
      assert (when_nothing_satisfies_p f sl ac);
      assert (equal s sl); // required
      assert (equal (filter_loop f s i ac) ac) // required
   end

val filter:
   f:('a -> Tot bool) ->
   s:seq 'a ->
   Tot (s':seq 'a{filtered_p f s s'})
let filter f s =
   filter_loop_lemma f s 0 createEmpty;
   filter_loop f s 0 createEmpty
