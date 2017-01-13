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

module Flutterbye.Seq.Mem
open FStar.Seq
open Flutterbye.Seq.Contains

type mem_p (#a_t:Type) (a:a_t) (s:seq a_t) =
   (exists (x:nat).
      x < length s && index s x = a)

private val eq: 'a -> 'a -> Tot bool
let eq a_1 a_2 =
   a_1 = a_2

val mem: x:'a -> s:seq 'a -> Tot (b:bool{b <==> mem_p x s})
let mem a s =
   contains (eq a) s

abstract val index_lemma:
   s:seq 'a ->
   Lemma
      (ensures
         // an element obtained from a sequence is a member of that sequence.
         (length s > 0 ==>
            (forall (x:nat).
               x < length s ==> mem_p (index s x) s)))
let index_lemma s =
   Flutterbye.Seq.Contains.index_lemma s

abstract val slice_lemma:
   s:seq 'a ->
   Lemma
      (ensures
         (forall (x:nat) (y:nat).
            // if [x, y) describes a non-empty (where x < y) slice of `s`...
            (y <= length s /\ x < y) ==>
               // then any member of the slice is a member of `s`.
               (forall z.
                  mem_p z (slice s x y) ==> mem_p z s)))
let slice_lemma s =
   Flutterbye.Seq.Contains.slice_lemma s

private type empty_p (#a_t:Type) (s:seq a_t) =
   forall (x:a_t).
      ~ (mem_p x s)

abstract val empty_lemma:
   s:seq 'a ->
   Lemma (ensures (length s = 0 <==> empty_p s))
let empty_lemma s =
   Flutterbye.Seq.Contains.empty_lemma s

abstract val create_lemma:
   n:nat ->
   a:'a ->
   Lemma
      (ensures
         // if we are creating an empty sequence, then null membership applies.
         ((n = 0 <==> empty_p (create n a)) /\
         // otherwise, only `a` can be a member of the resulting sequence.
         (n > 0 <==> mem_p a (create n a))))
let create_lemma n a =
   Flutterbye.Seq.Contains.create_lemma n a

abstract val append_lemma:
      #a_t:Type
   -> s_1:seq a_t
   -> s_2:seq a_t
   -> Lemma
      (ensures
         (  (forall (a:a_t).
               mem_p a s_1 ==> mem_p a (append s_1 s_2))
         \/ (forall (a:a_t).
               mem_p a s_2 ==> mem_p a (append s_1 s_2))
            // the following clause isn't successfully proven without the previous two.
         \/ (forall (a:a_t).
               mem_p a (append s_1 s_2) <==> (mem_p a s_1 \/ mem_p a s_2))
         )
      )
let append_lemma #a_t s_1 s_2 =
   Flutterbye.Seq.Contains.append_lemma s_1 s_2
