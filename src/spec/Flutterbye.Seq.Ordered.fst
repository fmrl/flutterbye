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

private type reflexive_p (#a_t:Type) (f:cmp_t a_t) (s:seq a_t)  =
   forall x.
      mem_p x s ==> b2t (f x x)

private type antisymmetric_p (#a_t:Type) (f:cmp_t a_t) (s:seq a_t) =
   length s = 0 \/
   (forall x y.
      mem_p x s /\ mem_p y s ==> (f x y && f y x <==> y = x))

private type transitive_p (#a_t:Type) (f:cmp_t a_t) (s:seq a_t) =
   forall x y z.
      mem_p x s /\ mem_p y s /\ mem_p z s /\ b2t (f x y && f y z) ==> f x z

private type sequenced_p (#a_t:Type) (f:cmp_t a_t) (s:seq a_t) =
   length s < 2
   \/ (forall (x:nat) (y:nat).
         (x < length s && y < length s && x < y)
         ==> (
            x < length s && y < length s
            && (
               let a_x = index s x in
               let a_y = index s y in
               not (f a_y a_x) && (f a_x a_y)
            )
         )
      )

type pordered_p (#a_t:Type) (f:cmp_t a_t) (s:seq a_t) =
   reflexive_p f s
   /\ antisymmetric_p f s
   /\ transitive_p f s
   /\ sequenced_p f s

private val reflexive_loop:
   f:cmp_t 'a ->
   s:seq 'a ->
   i:nat{i <= length s /\ reflexive_p f (slice s 0 i)} ->
   Tot (b:bool{b2t b <==> reflexive_p f s})
      (decreases (length s - i))
let rec reflexive_loop f s i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a = index s i in
      if f a a then
         reflexive_loop f s (i + 1)
      else
         false
   else
      true

private type antisymmetric_inner_p (#a_t:Type) (f:cmp_t a_t) (s:seq a_t) (a:a_t) =
   forall x.
      mem_p x s ==> (f x a && f a x <==> mem_p x s /\ a = x)

private val antisymmetric_inner_loop:
   f:cmp_t 'a ->
   s:seq 'a ->
   a:'a ->
   i:nat{i <= length s /\ antisymmetric_inner_p f (slice s 0 i) a} ->
   Tot (b:bool{b2t b <==> antisymmetric_inner_p f s a})
      (decreases (length s - i))
let rec antisymmetric_inner_loop f s a i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a' = index s i in
      if (a = a') = (f a a' && f a' a) then
         antisymmetric_inner_loop f s a (i + 1)
      else
         false
   else
      true

private val antisymmetric_loop:
   f:cmp_t 'a ->
   s:seq 'a ->
   i:nat{i <= length s /\ antisymmetric_p f (slice s 0 i)} ->
   Tot (b:bool{b2t b <==> antisymmetric_p f s})
      (decreases (length s - i))
let rec antisymmetric_loop f s i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a = index s i in
      if antisymmetric_inner_loop f s a 0 then
         antisymmetric_loop f s (i + 1)
      else
         false
   else
      true

private type transitive_loop_z_p (#a_t:Type) (f:cmp_t a_t) (s:seq a_t) (a_1:a_t) (a_2:a_t) =
   forall z.
      (mem_p z s /\ b2t (f a_1 a_2 && f a_2 z)) ==> f a_1 z

private val transitive_loop_z:
   f:cmp_t 'a ->
   s:seq 'a ->
   a_1:'a ->
   a_2:'a ->
   i:nat{i <= length s /\ transitive_loop_z_p f (slice s 0 i) a_1 a_2} ->
   Tot (b:bool{b2t b <==> transitive_loop_z_p f s a_1 a_2})
      (decreases (length s - i))
let rec transitive_loop_z f s a_1 a_2 i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a_3 = index s i in
      if f a_1 a_2 && f a_2 a_3 then
         f a_1 a_3 && transitive_loop_z f s a_1 a_2 (i + 1)
      else
         transitive_loop_z f s a_1 a_2 (i + 1)
   else
      true

private type transitive_loop_yz_p
      (#a_t:Type)
      (f:cmp_t a_t)
      (s:seq a_t)
      (a_1:a_t)
      (i:nat{i <= length s})
      =
   forall y z.
      (
         mem_p y (slice s 0 i)
         /\ mem_p z s
         /\ b2t (f a_1 y && f y z)
      )
      ==> f a_1 z

private val transitive_loop_yz:
   f:cmp_t 'a ->
   s:seq 'a ->
   a_1:'a ->
   i:nat{i <= length s /\ transitive_loop_yz_p f s a_1 i} ->
   Tot (b:bool{b2t b <==> transitive_loop_yz_p f s a_1 (length s)})
      (decreases (length s - i))
let rec transitive_loop_yz f s a_1 i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a_2 = index s i in
      if transitive_loop_z f s a_1 a_2 0 then
         transitive_loop_yz f s a_1 (i + 1)
      else
         false
   else
      true

private type transitive_loop_xyz_p
      (#a_t:Type)
      (f:cmp_t a_t)
      (s:seq a_t)
      (i:nat{i <= length s})
      =
   forall x y z. (
      mem_p x (slice s 0 i)
      /\ mem_p y s
      /\ mem_p z s
      /\ b2t (f x y && f y z)
   )
   ==> f x z

private val transitive_loop_xyz:
   f:cmp_t 'a ->
   s:seq 'a ->
   i:nat{i <= length s /\ transitive_loop_xyz_p f s i} ->
   Tot (b:bool{b2t b <==> transitive_loop_xyz_p f s (length s)})
      (decreases (length s - i))
let rec transitive_loop_xyz f s i =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a_1 = index s i in
      if transitive_loop_yz f s a_1 0 then
         transitive_loop_xyz f s (i + 1)
      else
         false
   else
      true

private val transitive:
   f:cmp_t 'a ->
   s:seq 'a ->
   Tot (b:bool{b2t b <==> transitive_p f s})
let transitive f s =
   transitive_loop_xyz f s 0

private type sequenced_loop_p (#a_t:Type) (f:cmp_t a_t) (s:seq a_t) (i:nat{i <= length s}) =
   i < 2
   \/ (forall (x:nat) (y:nat).
         (x < i && y < i && x < y)
         ==> (
            x < i && y < i
            && (
               let a_x = index s x in
               let a_y = index s y in
               not (f a_y a_x) && (f a_x a_y)
            )
         )
      )

private val sequenced_loop:
   f:cmp_t 'a ->
   s:seq 'a{transitive_p f s} ->
   i:nat{i <= length s /\ sequenced_loop_p f s i} ->
   Tot (b:bool{b2t b <==> sequenced_loop_p f s (length s)})
      (decreases (length s - i))
let rec sequenced_loop f s i =
   if i < length s then
      begin
         if i = 0 then
            sequenced_loop f s 1
         else
            let a_0 = index s (i - 1) in
            let a_i = index s i in
            if not (f a_i a_0) && (f a_0 a_i) then
               sequenced_loop f s (i + 1)
            else
               false
      end
   else
      true

private val sequenced:
   f:cmp_t 'a ->
   s:seq 'a{transitive_p f s} ->
   Tot (b:bool{b2t b <==> sequenced_p f s})
let rec sequenced f s =
   sequenced_loop f s 0

val pordered: f:cmp_t 'a -> s:seq 'a -> Tot (b:bool{b2t b <==> pordered_p f s})
let pordered f s =
   reflexive_loop f s 0
   && antisymmetric_loop f s 0
   && transitive f s
   && sequenced f s

abstract val slice_lemma:
   f:cmp_t 'a ->
   s:seq 'a{pordered_p f s} ->
   Lemma
      (ensures
         (forall (x:nat) (y:nat).
            // if [x, y) describe a slice of `s`, then that slice is also partially ordered.
            y <= length s && x <= y ==> pordered_p f (slice s x y)))
let slice_lemma f s =
   ()

private val append_lemma_for_sequenced:
   f:cmp_t 'a ->
   s_1:seq 'a{sequenced_p f s_1} ->
   s_2:seq 'a{sequenced_p f s_2} ->
   Lemma
      (ensures (sequenced_p f (append s_1 s_2)))
let append_lemma_for_sequenced f s_1 s_2 =
   if length s_1 = 0 || length s_2 = 0 then
      ()
   else
      admit ()

abstract val append_lemma:
   f:cmp_t 'a ->
   s_1:seq 'a{pordered_p f s_1} ->
   s_2:seq 'a{pordered_p f s_2} ->
   Lemma
(*      (requires (
         length s_1 > 0  && length s_2 > 0
         ==> (
            let a_1 = index s_1 (length s_1 - 1) in
            let a_2 = index s_2 0 in
            not (f a_2 a_1) && (f a_1 a_2)
         )
      ))*)
      //(requires (sequenced_p f (append s_1 s_2))) // needed to prove.
      (ensures (pordered_p f (append s_1 s_2)))
let append_lemma f s_1 s_2 =
   append_lemma_for_sequenced f s_1 s_2



