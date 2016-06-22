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

module Flutterbye.Seq.Unique
open FStar.Seq

type unique_p (#a_t:Type) (s:seq a_t) =
   0 = length s \/
   (forall (x:nat) (y:nat).
      x < length s && y < length s && index s y = index s x <==>
         x < length s && y < length s && y = x)

abstract val slice_lemma:
   s:seq 'a{unique_p s} ->
   Lemma
      (ensures
         (forall (x:nat) (y:nat) (sl:seq 'a).
            // if [x, y) describe a slice of `s`, `sl`, then that slice is unique.
            (y < length s /\ x <= y /\ FStar.Seq.equal sl (slice s x y)) ==> unique_p sl))
let slice_lemma s =
   ()

(*abstract val append_lemma:
   s_1:seq 'a{unique_p s_1} ->
   s_2:seq 'a{unique_p s_2} ->
   Lemma
      //(requires (Flutterbye.Seq.Disjoint.disjoint_p s_1 s_2))
      (ensures (unique_p (append s_1 s_2)))
let append_lemma s_1 s_2 =
   ()*)

abstract val create_lemma:
   n:nat ->
   a:'a ->
   Lemma
      (ensures (n <= 1 <==> unique_p (create n a)))
let create_lemma n a =
   let s = create n a in
   if n <= 1 then
      ()
   else
      assert (index s 0 = index s 1) // required witness

private val unique_loop:
   s:seq 'a ->
   i:nat{i <= length s} ->
   Tot bool
      (decreases (length s - i))
let rec unique_loop s i =
   if i < length s then
      let a = index s i in
      if Flutterbye.Seq.Mem.mem a (slice s 0 i) then
         false
      else
         unique_loop s (i + 1)
   else
      true

private val unique_lemma:
   s:seq 'a ->
   i:nat{i <= length s} ->
   Lemma
      (requires (unique_p (slice s 0 i)))
      (ensures (b2t (unique_loop s i) <==> unique_p s))
      (decreases (length s - i))
let rec unique_lemma s i =
   if i < length s then
      let a = index s i in
      if Flutterbye.Seq.Mem.mem a (slice s 0 i) then
         ()
      else
         (assert (unique_p (create 1 (index s i))); // learned through create_lemma.
         unique_lemma s (i + 1))
   else
      ()

val unique: s:seq 'a -> Tot (b:bool{b <==> unique_p s})
let unique s =
   unique_lemma s 0;
   unique_loop s 0

private type deduped_p (#a_t:Type) (s:seq a_t) (s':seq a_t) =
   unique_p s' /\
   length s' <= length s /\
   length s = 0 <==> length s' = 0 /\
   (forall x.
      Flutterbye.Seq.Mem.mem_p x s <==> Flutterbye.Seq.Mem.mem_p x s')

private val dedup_loop:
   s:seq 'a ->
   i:nat{i <= length s} ->
   ac:seq 'a ->
   Tot (ac':seq 'a)
      (decreases (length s - i))
let rec dedup_loop s i ac =
   if i < length s then
      let a = index s i in
      let ac' =
         if Flutterbye.Seq.Mem.mem a ac then
            ac
         else
            append ac (create 1 a) in
      dedup_loop s (i + 1) ac'
   else
      ac

private val dedup_lemma:
   s:seq 'a ->
   i:nat{i <= length s} ->
   ac:seq 'a ->
   Lemma
      (requires (deduped_p (slice s 0 i) ac))
      (ensures (deduped_p s (dedup_loop s i ac)))
      (decreases (length s - i))
let rec dedup_lemma s i ac =
   if i < length s then
      let a = index s i in
      let ac' =
         if Flutterbye.Seq.Mem.mem a ac then
            ac
         else
            append ac (create 1 a) in
      dedup_lemma s (i + 1) ac'
   else
      ()

val dedup: (s:seq 'a) -> Tot (s':seq 'a{deduped_p s s'})
let dedup s =
   dedup_lemma s 0 createEmpty;
   dedup_loop s 0 createEmpty
