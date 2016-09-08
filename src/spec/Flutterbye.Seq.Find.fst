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

module Flutterbye.Seq.Find
open FStar.Seq
open Flutterbye.Option
open Flutterbye.Seq.Remove

private type find_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (i:option nat) =
      // if `s` is of length zero, the only outcome can be `None`.
      ((length s = 0) ==> is_None i)
      // `None` signifies that no element is `s` can satisfy predicate `f` 
   /\ (is_None i ==> ~ (exists (x:nat{x < length s}). f (index s x)))
      // `Some i` implies that the length of `s` must be non-zero.
   /\ (is_Some i ==> b2t (length s > 0))
      // `Some i` implies that `i` must be a valid index of `s`.
   /\ (is_Some i ==> b2t (get i < length s))
      // `Some i` implies that `i` must index an element within `s` that satisfies
      // predicate `f`.
   /\ (is_Some i ==> b2t (f (index s (get i))))
      // `Some` implies that there exists an element that can satisfy 
      // predicate `f`.
      // todo: can this be turned into an iff?
   /\ (is_Some i ==> (exists (x:nat{x < length s}). f (index s x)))
      // `Some i` implies, if `i > 0` that all elements preceeding `i`
      // must not satisfy predicate `f`.
   /\ (   (is_Some i && get i > 0) 
      ==> (forall (x:nat). x < get i ==> not (f (index s x)))
      )
      
private val find_loop:
   f:('a -> Tot bool) 
   -> s:seq 'a 
   -> i:nat{i <= length s} 
   -> ac:option nat 
   -> Tot (ac':option nat)
      (decreases (length s - i))
let rec find_loop f s i ac =
   if i = length s then
      ac
   else
      let ac' =
         if is_None ac then begin
            if f (index s i) then
               Some i
            else
               None
         end 
         else
            ac 
      in
      find_loop f s (i + 1) ac'

private val find_lemma:
      f:('a -> Tot bool)
   -> s:seq 'a 
   -> i:nat{i <= length s} 
   -> ac:(option nat) 
   -> Lemma
      (requires (find_p f (slice s 0 i) ac))
      (ensures (find_p f s (find_loop f s i ac)))
      (decreases (length s - i))
let rec find_lemma f s i ac =
   let sl = slice s 0 i in
   if i = length s then begin
      if length s = 0 || is_Some ac then
         ()
      else begin
         assert (equal sl s); // required
         assert (~ (exists (x:nat{x < length s}). f (index s x)))
      end
   end
   else
      let ac' =
         let sl' = slice s 0 (i + 1) in
         if is_None ac then begin
            if f (index s i) then begin
               assert (index sl' i = index s i); // required
               assert (exists (x:nat{x < length sl'}). f (index sl' x));
               // the following assertion is required to prove the statement in find_p 
               // about all elements preceeding `i` not satisfying predicate `f`.
               assert (equal sl' (append sl (create 1 (index s i))));
               Some i
            end
            else begin
               assert (equal sl' (append sl (create 1 (index s i)))); // required
               assert (~ (exists (x:nat{x < length sl'}). f (index sl' x)));
               None
            end
         end 
         else begin
            assert (index sl' (get ac) = index s (get ac)); // required
            assert (exists (x:nat{x < length sl'}). f (index sl' x));
            ac
         end
      in 
      find_lemma f s (i + 1) ac'

val find: 
      f:('a -> Tot bool) 
   -> s:seq 'a 
   -> Tot (i:option nat{find_p f s i})
let find f s =
   find_lemma f s 0 None;
   find_loop f s 0 None

private type empty_p (#a_t:Type) (s:seq a_t) =
   forall (f:a_t -> Tot bool).
      find_p f s None

// this function is used as a witness
private val eq: 'a -> 'a -> Tot bool
let eq a_1 a_2 =
   a_1 = a_2

abstract val empty_lemma:
      s:seq 'a 
   -> Lemma (ensures (length s = 0 <==> empty_p s))
let empty_lemma s =
   if length s = 0 then
      ()
   else begin
      assert (find_p (eq (index s 0)) s (Some 0)); // required witness
      assert (~ (empty_p s))
   end

private type found_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) =
   ~ (find_p f s None)

abstract val create_lemma:
      n:nat
   -> a:'a 
   -> Lemma
      (ensures
         (  // if we are creating an empty sequence, then the empty rule applies.
            (n = 0 <==> (forall (f:'a -> Tot bool). empty_p (create n a)))
         /\ // otherwise, `f a` is the identical to `found_p f s`.
            (n > 0 ==> (forall (f:'a -> Tot bool). (f a <==> found_p f (create n a))))))
let create_lemma n a =
   if n = 0 then
      ()
   else begin
      let s = create n a in
      let a = index s 0 in
      let f = eq a in
      assert (f a <==> found_p f s) // required witness.
   end
(*
private val append_lemma_found2:
      s_1:seq 'a 
   -> s_2:seq 'a
   -> Lemma
      (requires (True))
      (ensures
         // if a value can be found in the second sequence, the value can be found in
         // the the "appended" sequence.
         (forall (f:'a -> Tot bool).
            (found_p f s_2 ==> found_p f (append s_1 s_2)))
      )
let append_lemma_found2 s_1 s_2 =
   admit () // todo: proof needed.
   *)

abstract val append_lemma:
      s_1:seq 'a 
   -> s_2:seq 'a
   -> Lemma
      (ensures
         (  // if a value can be found in the first sequence, finding the same value
            // in the "appended" sequence will yield a successful search with the
            // same index.
            (forall (f:'a -> Tot bool) (i:nat{i < length s_1}).
               (find_p f s_1 (Some i) ==> find_p f (append s_1 s_2) (Some i)))
            // if a value can be found in the first sequence, the value can be found in
            // the the "appended" sequence.
         // /\ (forall (f:'a -> Tot bool). (found_p f s_1 ==> found_p f (append s_1 s_2)))
            // if a value cannot be found in the first sequence but can be found in the
            // second seqence, finding the same value in the "appended" sequence will 
            // yield a successful search with the index shifted by the length of the first
            // sequence.
         // /\ (forall (f:'a -> Tot bool) (i:nat{i < length s_1}).
         //       (   (~ (found_p f s_1) /\ (find_p f s_2 (Some i))) 
         //       ==> find_p f (append s_1 s_2) (Some (i + length s_1))))
            // if a value can be found in the second sequence, the value can be found in
            // the the "appended" sequence.
         // /\ (forall (f:'a -> Tot bool).
         //    (found_p f s_2 ==> found_p f (append s_1 s_2)))
            // if the value can be found in one of the two input sequences, the value will be
            // found in the "appended" sequence, and vice versa.
         // /\ (forall (f:'a -> Tot bool).
         //      (found_p f (append s_1 s_2) <==> (found_p f s_1 \/ found_p f s_2)))
         )
      )
let append_lemma s_1 s_2 =
   let s' = append s_1 s_2 in
   assert (equal (slice s' 0 (length s_1)) s_1)
   //append_lemma_found2 s_1 s_2

(*
val remove_lemma:
      s:seq 'a{length s > 0}
   -> i:nat{i < length s}
   -> f:('a -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures
         (  // if the input sequence doesn't have an element that satisfies 
            // `f` then the output won't either.
            (~ (found_p f s)) ==> (~ (found_p f (remove s i)))
            // if an element in the input sequence that satisfies `f` can be
            // found and the index of that element appears before the element
            // being removed, the result of calling `find` on the output 
            // sequence won't be different from calling it on the input 
            // sequence.  
         /\ ((found_p f s /\ get (find f s) < i) ==> (get (find f (remove s i)) = get (find f s)))  
            // if an element in the input sequence that satisfies `f` can be
            // found and the index of that element appears after the element
            // being removed, the result of calling `find` on the output 
            // sequence will be one less than the result of calling it on 
            // the input sequence.  
         /\ ((found_p f s /\ get (find f s) > i) ==> (get (find f (remove s i)) = get (find f s) - 1))  
            // if an element in the input sequence that satisfies `f` can be
            // found and that is the element being removed, the result of 
            // calling `find` on the output sequence will match the output of
            // calling find on the slice of the sequence following the element
            // being removed.  
         /\ (   (found_p f s /\ get (find f s) = i) 
            ==> (get (find f (remove s i)) = get (find f (slice s (i + 1) (length s))))
            )  
            // if an element in the input sequence that satisfies `f` can be
            // found and that element is not being removed from the sequence,
            // the output sequence will also have an element that satisfies 
            // `f`.  
         /\ ((found_p f s /\ get (find f s) <> i) ==> found_p f (remove s i))  
         )
      ) 
let remove_lemma f s i =
   ()*)