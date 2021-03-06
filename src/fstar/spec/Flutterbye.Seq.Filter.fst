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
open Flutterbye.Seq.Contains

// the output sequence will not be longer than the input sequence.
private type never_emits_longer_p (#t:Type) (s:seq t) (u:seq t) =
   b2t (length u <= length s)

// the output sequence is empty iff no element of `s` satisfies `f`.
private type emits_empty_p
   (#t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
   (u:seq t)
=
   ~ (contains_p f s) <==> b2t (length u = 0)

// the output sequence must be shorter than the input sequence iff
// at least one element doesn't satisfy `f`.
private type emits_subset_p
   (#t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
   (u:seq t)
=
   contains_p (fun x -> not (f x)) s <==> b2t (length u < length s)

// the output sequence only contains elements that satisfy `f`.
private type emits_satisfying_p
   (#a_t:Type)
   (f:(a_t -> Tot bool))
   (u:seq a_t)
=
   forall (i:nat{i < length u}).
      f (index u i)

type filter_p (#t:Type) (f:(t -> Tot bool)) (s:seq t) (u:seq t) =
      never_emits_longer_p s u
   /\ emits_empty_p f s u
   /\ emits_subset_p f s u
   /\ emits_satisfying_p f u

private val filter_loop:
      t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> i:nat{i <= length s}
   -> accum:seq t{filter_p f (slice s 0 i) accum}
   -> Tot (u:seq t{filter_p f s u})
      (decreases (length s - i))
let rec filter_loop t f s i accum =
   let s_0 = slice s 0 i in
   if i = length s then begin
      assert (equal s s_0);
      accum
   end
   else begin
      let s_1 = slice s 0 (i + 1) in
      assert (equal s_0 (slice s_1 0 i));
      let x = index s i in
      if f x then begin
         let accum' = append accum (create 1 x) in
         assert (b2t (f (index s_1 i)));
         Flutterbye.Seq.Contains.slice_lemma s_1 0 i (fun x -> not (f x));
         assert (
                contains_p (fun x -> not (f x)) s_0
            ==> contains_p (fun x -> not (f x)) s_1
         );
         assert (
                ~ (contains_p (fun x -> not (f x)) s_0)
            ==> ~ (contains_p (fun x -> not (f x)) s_1)
         );
         assert (filter_p f s_1 accum');
         filter_loop t f s (i + 1) accum'
      end
      else begin
         assert (b2t (not (f (index s_1 i))));
         Flutterbye.Seq.Contains.slice_lemma s_1 0 i f;
         assert (contains_p f s_0 ==> contains_p f s_1);
         assert (~ (contains_p f s_0) ==> ~ (contains_p f s_1));
         assert (filter_p f s_1 accum);
         filter_loop t f s (i + 1) accum
      end
   end

val filter:
      #t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> Tot (u:seq t{filter_p f s u})
let filter #t f s =
   filter_loop t f s 0 createEmpty

private type bisection_p
   (t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
=
   forall (i:nat{i <= length s}).
      equal
         (filter f s)
         (append
            (filter f (slice s 0 i))
            (filter f (slice s i (length s))))

private val bisection_lemma:
   t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> i:nat{i <= length s}
   -> Lemma
      (requires (bisection_p t f (slice s 0 i)))
      (ensures (bisection_p t f s))
      (decreases (length s - i))
let rec bisection_lemma t f s i =
   let s_i = slice s 0 i in
   if i = length s then begin
      assert (equal s_i s);
      ()
   end
   else begin
      let (i':nat{i' <= length s}) = i + 1 in
      let s_i' = slice s 0 i' in
      assert (equal s_i (slice s_i' 0 i));
      let x = index s i in
      if f x then begin
         admit ();
         bisection_lemma t f s i'
      end
      else begin
         //admitP (equal (filter f s_i) (filter f s_i'));
         admit ();
         bisection_lemma t f s i'
      end
   end

abstract val append_lemma:
   #t:Type
   -> s_1:seq t
   -> s_2:seq t
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (
            equal
               (filter f (append s_1 s_2))
               (append (filter f s_1) (filter f s_2))
         )
      )
let append_lemma #t s_1 s_2 f =
   let s_3 = append s_1 s_2 in
   if length s_1 = 0 then
      assert (equal s_3 s_2)
   else begin
      if length s_2 = 0 then
         assert (equal s_3 s_1)
      else begin
         let u_1 = filter f s_1 in
         let u_2 = filter f s_2 in
         let u_3 = append u_1 u_2 in
         let v_3 = filter f s_3 in
         bisection_lemma t f s_3 0;
         assert (equal s_1 (slice s_3 0 (length s_1)));
         assert (equal s_2 (slice s_3 (length s_1) (length s_3)));
         assert (equal v_3 u_3)
      end
   end
