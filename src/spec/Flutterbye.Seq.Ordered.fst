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
open Flutterbye.Seq.Mem

type cmp_t 'a = 'a -> 'a -> Tot bool

private type reflexive_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t)  =
   forall x.
      mem_p x s ==> b2t (lte x x)

private type antisymmetric_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t) =
   length s = 0 \/
   (forall (x:a_t{mem_p x s}) (y:a_t{mem_p y s}).
      (lte x y && lte y x) <==> (y = x))

private type transitive_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t) =
   forall x y z.
      mem_p x s /\ mem_p y s /\ mem_p z s /\ b2t (lte x y && lte y z) ==> lte x z

private type sequenced_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t) =
   forall (x:nat{x < length s}) (y:nat{y < length s}).
      (x <= y) <==> (lte (index s x) (index s y))

type pordered_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t) =
   reflexive_p lte s
   /\ antisymmetric_p lte s
   /\ transitive_p lte s
   /\ sequenced_p lte s

private val reflexive_loop:
   lte:cmp_t 'a ->
   s:seq 'a ->
   i:nat{i <= length s /\ reflexive_p lte (slice s 0 i)} ->
   Tot (b:bool{b2t b <==> reflexive_p lte s})
      (decreases (length s - i))
let rec reflexive_loop lte s i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a = index s i in
      if lte a a then
         reflexive_loop lte s (i + 1)
      else
         false
   else
      true

private type antisymmetric_inner_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t) (a:a_t) =
   forall x.
      mem_p x s ==> (lte x a && lte a x <==> mem_p x s /\ a = x)

private val antisymmetric_inner_loop:
   lte:cmp_t 'a ->
   s:seq 'a ->
   a:'a ->
   i:nat{i <= length s /\ antisymmetric_inner_p lte (slice s 0 i) a} ->
   Tot (b:bool{b2t b <==> antisymmetric_inner_p lte s a})
      (decreases (length s - i))
let rec antisymmetric_inner_loop lte s a i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a' = index s i in
      if (a = a') = (lte a a' && lte a' a) then
         antisymmetric_inner_loop lte s a (i + 1)
      else
         false
   else
      true

private val antisymmetric_loop:
   lte:cmp_t 'a ->
   s:seq 'a ->
   i:nat{i <= length s /\ antisymmetric_p lte (slice s 0 i)} ->
   Tot (b:bool{b2t b <==> antisymmetric_p lte s})
      (decreases (length s - i))
let rec antisymmetric_loop lte s i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a = index s i in
      if antisymmetric_inner_loop lte s a 0 then
         antisymmetric_loop lte s (i + 1)
      else
         false
   else
      true

private type transitive_loop_z_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t) (a_1:a_t) (a_2:a_t) =
   forall z.
      (mem_p z s /\ b2t (lte a_1 a_2 && lte a_2 z)) ==> lte a_1 z

private val transitive_loop_z:
   lte:cmp_t 'a ->
   s:seq 'a ->
   a_1:'a ->
   a_2:'a ->
   i:nat{i <= length s /\ transitive_loop_z_p lte (slice s 0 i) a_1 a_2} ->
   Tot (b:bool{b2t b <==> transitive_loop_z_p lte s a_1 a_2})
      (decreases (length s - i))
let rec transitive_loop_z lte s a_1 a_2 i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a_3 = index s i in
      if lte a_1 a_2 && lte a_2 a_3 then
         lte a_1 a_3 && transitive_loop_z lte s a_1 a_2 (i + 1)
      else
         transitive_loop_z lte s a_1 a_2 (i + 1)
   else
      true

private type transitive_loop_yz_p
      (#a_t:Type)
      (lte:cmp_t a_t)
      (s:seq a_t)
      (a_1:a_t)
      (i:nat{i <= length s})
      =
   forall y z.
      (
         mem_p y (slice s 0 i)
         /\ mem_p z s
         /\ b2t (lte a_1 y && lte y z)
      )
      ==> lte a_1 z

private val transitive_loop_yz:
   lte:cmp_t 'a ->
   s:seq 'a ->
   a_1:'a ->
   i:nat{i <= length s /\ transitive_loop_yz_p lte s a_1 i} ->
   Tot (b:bool{b2t b <==> transitive_loop_yz_p lte s a_1 (length s)})
      (decreases (length s - i))
let rec transitive_loop_yz lte s a_1 i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a_2 = index s i in
      if transitive_loop_z lte s a_1 a_2 0 then
         transitive_loop_yz lte s a_1 (i + 1)
      else
         false
   else
      true

private type transitive_loop_xyz_p
      (#a_t:Type)
      (lte:cmp_t a_t)
      (s:seq a_t)
      (i:nat{i <= length s})
      =
   forall x y z. (
      mem_p x (slice s 0 i)
      /\ mem_p y s
      /\ mem_p z s
      /\ b2t (lte x y && lte y z)
   )
   ==> lte x z

private val transitive_loop_xyz:
   lte:cmp_t 'a ->
   s:seq 'a ->
   i:nat{i <= length s /\ transitive_loop_xyz_p lte s i} ->
   Tot (b:bool{b2t b <==> transitive_loop_xyz_p lte s (length s)})
      (decreases (length s - i))
let rec transitive_loop_xyz lte s i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a_1 = index s i in
      if transitive_loop_yz lte s a_1 0 then
         transitive_loop_xyz lte s (i + 1)
      else
         false
   else
      true

private val transitive:
   lte:cmp_t 'a ->
   s:seq 'a ->
   Tot (b:bool{b2t b <==> transitive_p lte s})
let transitive lte s =
   transitive_loop_xyz lte s 0

private type sequenced_loop2_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t) (y:nat{y < length s}) (i:nat{i <= length s}) =
   forall (x:nat{x < i}).
      (x <= y) <==> (lte (index s x) (index s y))



private val sequenced_loop2:
   lte:cmp_t 'a ->
   s:seq 'a ->
   y:nat{y < length s} ->
   i:nat{i <= length s /\ sequenced_loop2_p lte s y i} ->
   Tot (b:bool{b2t b <==> sequenced_loop2_p lte s y (length s)})
      (decreases (length s - i))
let rec sequenced_loop2 lte s y i =
   if i < length s then
      begin
         if (i <= y) = (lte (index s i) (index s y)) then
            sequenced_loop2 lte s y (i + 1)
         else
            false
      end
   else
      true

private type sequenced_loop1_p (#a_t:Type) (lte:cmp_t a_t) (s:seq a_t) (i:nat{i <= length s}) =
   forall (x:nat{x < length s}) (y:nat{y < i}).
      (x <= y) <==> (lte (index s x) (index s y))

private val sequenced_loop1:
   lte:cmp_t 'a ->
   s:seq 'a ->
   i:nat{i <= length s /\ sequenced_loop1_p lte s i} ->
   Tot (b:bool{b2t b <==> sequenced_loop1_p lte s (length s)})
      (decreases (length s - i))
let rec sequenced_loop1 lte s i =
   if i < length s then
      begin
         if sequenced_loop2 lte s i 0 then
            sequenced_loop1 lte s (i + 1)
         else
            false
      end
   else
      true

private val sequenced:
   lte:cmp_t 'a ->
   s:seq 'a ->
   Tot (b:bool{b2t b <==> sequenced_p lte s})
let rec sequenced lte s =
   sequenced_loop1 lte s 0

val pordered: lte:cmp_t 'a -> s:seq 'a -> Tot (b:bool{b2t b <==> pordered_p lte s})
let pordered lte s =
   reflexive_loop lte s 0
   && antisymmetric_loop lte s 0
   && transitive lte s
   && sequenced lte s

abstract val slice_lemma:
   lte:cmp_t 'a ->
   s:seq 'a{pordered_p lte s} ->
   Lemma
      (ensures
         (forall (x:nat) (y:nat).
            // if [x, y) describe a slice of `s`, then that slice is also partially ordered.
            y <= length s && x <= y ==> pordered_p lte (slice s x y)))
let slice_lemma lte s =
   ()

abstract val append_lemma_antisymmetry:
   lte:cmp_t 'a ->
   s_1:seq 'a{pordered_p lte s_1} ->
   s_2:seq 'a{pordered_p lte s_2} ->
   Lemma
      (ensures (antisymmetric_p lte (append s_1 s_2)))
let append_lemma_antisymmetry lte s_1 s_2 =
   admit ()

abstract val append_lemma_transitivity:
   lte:cmp_t 'a ->
   s_1:seq 'a{pordered_p lte s_1} ->
   s_2:seq 'a{pordered_p lte s_2} ->
   Lemma
      (ensures (transitive_p lte (append s_1 s_2)))
let append_lemma_transitivity lte s_1 s_2 =
   admit ()

abstract val append_lemma_sequencing:
   lte:cmp_t 'a ->
   s_1:seq 'a{pordered_p lte s_1} ->
   s_2:seq 'a{pordered_p lte s_2} ->
   Lemma
      (requires (
         // either `s_1` or `s_2` are of zero length
         length s_1 = 0 || length s_2 = 0
         // or the first element of `s_2` must not be less than the final element of `s_1`.
         || lte (index s_1 (length s_1 - 1)) (index s_2 0)
      ))
      (ensures (sequenced_p lte (append s_1 s_2)))
let append_lemma_sequencing lte s_1 s_2 =
   let s' = append s_1 s_2 in
   assert (b2t (sequenced_loop1 lte s' 0))

abstract val append_lemma:
   lte:cmp_t 'a ->
   s_1:seq 'a{pordered_p lte s_1} ->
   s_2:seq 'a{pordered_p lte s_2} ->
   Lemma
      (ensures (pordered_p lte (append s_1 s_2)))
let append_lemma lte s_1 s_2 =
   if length s_1 > 0 && length s_2 > 0 then
      begin
         let s' = append s_1 s_2 in
         //assert (reflexive_p lte s'); // understood
         append_lemma_antisymmetry lte s_1 s_2;
         append_lemma_transitivity lte s_1 s_2;
         append_lemma_sequencing lte s_1 s_2;
         ()
      end
   else
      ()

      (*(requires (
         // either `s_1` or `s_2` are of zero length
         length s_1 = 0 || length s_2 = 0
         // or the first element of `s_2` must not be less than the final element of `s_1`.
         || lte (index s_1 (length s_1 - 1)) (index s_2 0)
      ))*)
