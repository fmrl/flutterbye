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

type found_p (#t:Type) (f:(t -> Tot bool)) (s:seq t) =
   exists (i:nat{i < length s}).
      f (index s i)

private type index_within_range_p (#t:Type) (s:seq t) (i:option nat) =
   b2t (Some? i) ==> b2t (get i < length s)

(*type found_implies_non_empty_p
   (#t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
   (i:option nat)
=
b2t (Some? i) ==> b2t (length s > 0) *)

private type index_satisfies_predicate_p
   (#t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
   (i:option nat{index_within_range_p s i})
=
   b2t (Some? i) ==> b2t (f (index s (get i)))

private type prefix_does_not_satisfy_predicate_p
   (t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
   (i:option nat{index_within_range_p s i})
=
   b2t (Some? i)
   ==>
      (forall (x:nat).
         b2t (x < get i) ==> b2t (not (f (index s x))))

private type find_p
   (#t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
   (i:option nat)
=
   (b2t (Some? i) <==> found_p f s)
   /\ (b2t (None? i) <==> ~ (found_p f s))
   /\ (b2t (length s = 0) ==> b2t (None? i))
   /\ index_within_range_p s i
//   /\ found_implies_non_empty_p f s i
   /\ index_satisfies_predicate_p f s i
   /\ prefix_does_not_satisfy_predicate_p t f s i

private val find_loop:
   t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> i:nat{i <= length s}
   -> accum:option nat{find_p f (slice s 0 i) accum}
   -> Tot (accum':option nat{find_p f s accum'})
      (decreases (length s - i))
let rec find_loop t f s i accum =
   let s_1 = slice s 0 i in
   if i = length s then begin
      assert (equal s_1 s);
      accum
   end
   else
      let accum' =
         let s_2 = slice s 0 (i + 1) in
         if None? accum then begin
            if f (index s i) then begin
               assert (index s_2 i == index s i); // required
               assert (found_p f s_2);
               // the following assertion is required to prove the statement in find_p
               // about all elements preceeding `i` not satisfying predicate `f`.
               assert (equal s_2 (append s_1 (create 1 (index s i))));
               Some i
            end
            else begin
               assert (equal s_2 (append s_1 (create 1 (index s i)))); // required
               assert (~ (found_p f s_2));
               None
            end
         end
         else begin
            assert (index s_2 (get accum) == index s (get accum)); // required
            assert (found_p f s_2);
            accum
         end
      in
      find_loop t f s (i + 1) accum'

val find:
   #t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> Tot (i:option nat{find_p f s i})
let find #t f s =
   find_loop t f s 0 None

val found:
   #t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> Tot (b:bool{b <==> found_p f s})
let found #t f s =
   Some? (find f s)

abstract val create_lemma:
   #t:Type
   -> n:nat
   -> x:t
   -> f:(t -> Tot bool)
   -> Lemma
      (ensures (
         (b2t (n = 0) ==> ~ (found_p f (create n x)))
         /\ (b2t (n > 0) ==> (b2t (f x) <==> found_p f (create n x)))
      ))
let create_lemma #t n x f =
   if n = 0 then
      ()
   else begin
      let s = create n x in
      assert (b2t (f x = f (index s 0)))
   end

abstract val append_lemma:
   #t:Type
   -> s_1:seq t
   -> s_2:seq t
   //-> f:(t -> Tot bool)
   -> Lemma
      (ensures
         (  // if a value can be found in the first sequence, finding the same value
            // in the "appended" sequence will yield a successful search with the
            // same index.
            (forall (f:t -> Tot bool) (i:nat{i < length s_1}).
               (find_p f s_1 (Some i) ==> find_p f (append s_1 s_2) (Some i)))
            // if a value can be found in the first sequence, the value can be found in
            // the the "appended" sequence.
         /\ (forall (f:t -> Tot bool). (found_p f s_1 ==> found_p f (append s_1 s_2)))
            // if a value cannot be found in the first sequence but can be found in the
            // second seqence, finding the same value in the "appended" sequence will
            // yield a successful search with the index shifted by the length of the first
            // sequence.
         /\ (forall (f:t -> Tot bool) (i:nat{i < length s_1}).
               (   (~ (found_p f s_1) /\ (find_p f s_2 (Some i)))
               ==> find_p f (append s_1 s_2) (Some (i + length s_1))))
            // if a value can be found in the second sequence, the value can be found in
            // the the "appended" sequence.
         /\ (forall (f:t -> Tot bool). (found_p f s_2 ==> found_p f (append s_1 s_2)))
            // if the value can be found in one of the two input sequences, the value will be
            // found in the "appended" sequence, and vice versa.
         /\ (forall (f:t -> Tot bool).
              (found_p f (append s_1 s_2) <==> (found_p f s_1 \/ found_p f s_2)))
         )
      )
let append_lemma #t s_1 s_2 =
   let s' = append s_1 s_2 in
   assert (equal (slice s' 0 (length s_1)) s_1); // required
   assert (equal (slice s' (length s_1) (length s')) s_2) // required

val equal_lemma:
   #t:Type
   -> s_1:seq t
   -> s_2:seq t
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (equal s_1 s_2))
      (ensures (find f s_1 = find f s_2))
let equal_lemma #t s_1 s_2 f =
   ()

// if a value cannot be found in sequence `s`, then it won't be found in any
// slice of `s` either.
private type slice_not_found_p
   (#t:Type)
   (s:seq t)
   (i:nat)
   (j:nat{i <= j && j <= length s})
   (f:t -> Tot bool)
=
   not (found f s) ==> not (found f (slice s i j))

private val slice_not_found_lemma:
   #t:Type
   -> s:seq t
   -> i:nat
   -> j:nat{i <= j && j <= length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (slice_not_found_p s i j f))
let slice_not_found_lemma #t s i j f =
   ()

// if there's an element at index `x` that satisfies `f` in sequence `s`, then any attempt
// to find an element in a slice delimited by `x` will fail.
private type slice_preceeding_p
   (#t:Type)
   (s:seq t)
   (i:nat)
   (j:nat{i <= j && j <= length s})
   (f:t -> Tot bool)
=
   (
       (exists (x:nat{x >= j}). find_p f s (Some x))
   ==> (not (found f (slice s i j)))
   )

private val slice_preceeding_lemma:
   #t:Type
   -> s:seq t
   -> i:nat
   -> j:nat{i <= j && j <= length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (slice_preceeding_p s i j f))
let slice_preceeding_lemma #t s i j f =
   ()

// if there's an element at index `x` that satisfies `f` in sequence `s` with in the range of
// a slice `s'` defined on the range `[i, j)` then the same `find` operation on `s'` will
// succeed, returning an index of `x - i`.
private type slice_inclusive_p
   (#t:Type)
   (s:seq t)
   (i:nat)
   (j:nat{i <= j && j <= length s})
   (f:t -> Tot bool)
=
   (found_p f s /\ b2t (i <= get (find f s)) /\ b2t (get (find f s) < j))
   ==> (
      found_p f (slice s i j)
      /\ b2t (get (find f (slice s i j)) = get (find f s) - i)
   )

private val slice_inclusive_lemma:
   #t:Type
   -> s:seq t
   -> i:nat
   -> j:nat{i <= j && j <= length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (slice_inclusive_p s i j f))
let slice_inclusive_lemma #t s i j f =
   let x = find f s in
   if Some? x && i <= get x && get x < j then
      begin
         let s' = slice s i j in
         let x' = find f s' in
         assert (equal (slice s i (get x)) (slice s' 0 ((get x) - i)));
         slice_preceeding_lemma s i (get x) f;
         admitP (Some? x')
      end
   else
      ()

abstract val slice_lemma:
   #t:Type
   -> s:seq t
   -> i:nat
   -> j:nat{i <= j && j <= length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures
         (  slice_not_found_p s i j f
         /\ slice_preceeding_p s i j f
         /\ slice_inclusive_p s i j f
         ///\ ((i = 0 && not (found f (slice s 0 j))) ==> slice_prefix_not_found_p s j f)
         )
      )
let slice_lemma #t s i j f =
   slice_not_found_lemma s i j f;
   slice_inclusive_lemma s i j f;
   slice_preceeding_lemma s i j f

// if the input sequence doesn't have an element that satisfies `f` then the
// output won't either.
private val remove_from_not_found_lemma:
   #t:Type
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (not (found f s)))
      (ensures (not (found f (remove s i))))
let remove_from_not_found_lemma #t s i f =
   ()

// if an element in the input sequence that satisfies `f` can be found and the
// index of that element appears before the element being removed, the result of
// calling `find` on the output sequence won't be different from calling it on
// the input sequence.
private type remove_from_prefix_p
   (#t:Type)
   (s:seq t{length s > 0})
   (i:nat{i < length s})
   (f:t -> Tot bool)
=
   (   (found f s && (get (find f s) < i))
   ==> (find f (remove s i) = find f s)
   )

private val remove_from_prefix_lemma:
   #t:Type
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (remove_from_prefix_p s i f))
let remove_from_prefix_lemma #t s i f =
   let s' = remove s i in
   let a = find f s in
   let a' = find f s' in
   if Some? a && get a < i then
      begin
         assert (equal (slice s 0 i) (slice s' 0 i));
         slice_lemma s 0 i f;
         assert (Some? a')
      end
   else
      ()

// if an element in the input sequence that satisfies `f` can be found and
// that element follows the element being removed from the sequence, the
// result of calling `find` on the output sequence will be one less than the
// result of calling it on the input sequence.
private type remove_from_suffix_p
   (#t:Type)
   (s:seq t{length s > 0})
   (i:nat{i < length s})
   (f:t -> Tot bool)
=
   (   (found f s && (get (find f s) > i))
   ==> (found f (remove s i) && (get (find f (remove s i)) = get (find f s) - 1))
   )

private val remove_from_suffix_lemma:
   #t:Type
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (remove_from_suffix_p s i f))
let remove_from_suffix_lemma #t s i f =
   let s' = remove s i in
   let a = find f s in
   let a' = find f s' in
   if Some? a && get a > i then
      begin
         assert (equal (slice s (i + 1) (length s)) (slice s' i (length s')));
         slice_lemma s (i + 1) (length s) f;
         assert (Some? a') // sub-goal
      end
   else
      ()

// if an element in the input sequence that satisfies `f` can be
// found and that element is not being removed from the sequence,
// the output sequence will also have an element that satisfies
// `f`.
private type remove_other_p
   (#t:Type)
   (s:seq t{length s > 0})
   (i:nat{i < length s})
   (f:t -> Tot bool)
=
   (found_p f s /\ get (find f s) <> i) ==> found_p f (remove s i)

private val remove_other_lemma:
   #t:Type
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (remove_other_p s i f))
let remove_other_lemma #t s i f =
   remove_from_prefix_lemma s i f;
   remove_from_suffix_lemma s i f;
   ()

private type remove_found_p
   (#t:Type)
   (s:seq t{length s > 0})
   (i:nat{i < length s})
   (f:t -> Tot bool)
=
   (   (found_p f s /\ get (find f s) = i)
   ==> (
          (~ (found_p f (slice s (i + 1) (length s))) <==> ~ (found_p f (remove s i)))
       /\ (
              (found_p f (slice s (i + 1) (length s)))
          ==> (get (find f (remove s i)) = i + get (find f (slice s (i + 1) (length s))))
          )
       )
   )

private val remove_found_lemma:
   #t:Type
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (remove_found_p s i f))
let remove_found_lemma #t s i f =
   let a = find f s in
   let s' = remove s i in
   if length s' = 0 then
      ()
   else
      begin
         let prefix = slice s 0 i in
         let suffix = slice s (i + 1) (length s) in
         if Some? a then
            begin
               if i = get a then
                  begin
                     let j = length prefix in
                     assert (equal prefix (slice s' 0 j));
                     assert (equal suffix (slice s' j (length s')));
                     if not (found f suffix) then
                        assert (not (found f prefix))
                     else
                        ()
                  end
               else
                  ()
            end
         else
            begin
               assert (None? (find f prefix));
               assert (None? (find f suffix))
            end
      end

abstract val remove_lemma:
   #t:Type
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures
         (  // remove_from_not_found
            ((not (found f s)) ==> (not (found f (remove s i))))
         /\ (remove_from_prefix_p s i f)
         /\ (remove_from_suffix_p s i f)
         /\ (remove_other_p s i f)
         /\ (remove_found_p s i f)
         )
      )
let remove_lemma #t s i f =
   begin
      if not (found f s) then
         remove_from_not_found_lemma s i f
      else
         ()
   end;
   remove_from_prefix_lemma s i f;
   remove_from_suffix_lemma s i f;
   remove_other_lemma s i f;
   remove_found_lemma s i f;
   ()
