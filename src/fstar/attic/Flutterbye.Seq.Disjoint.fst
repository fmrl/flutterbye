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

module Flutterbye.Seq.Disjoint
open FStar.Seq
open Flutterbye.Seq.Mem

// todo: /\ FStar.Set.equal empty (intersect (to_set s_1) (to_set s_2))
type disjoint_p (#a_t:Type) (s_1:seq a_t) (s_2:seq a_t) =
   forall x.
      ~ (mem_p x s_1 /\ mem_p x s_2)

private val disjoint_loop:
   s_1:seq 'a ->
   s_2:seq 'a ->
   i:nat{i <= length s_1} ->
   Tot bool
      (decreases (length s_1 - i))
let rec disjoint_loop s_1 s_2 i =
   if i < length s_1 then
      let a = index s_1 i in
      if mem a s_2 then
         false
      else
         disjoint_loop s_1 s_2 (i + 1)
   else
      true

private val disjoint_lemma:
   s_1:seq 'a ->
   s_2:seq 'a ->
   i:nat{i <= length s_1} ->
   Lemma
      (requires (disjoint_p (slice s_1 0 i) s_2))
      (ensures (b2t (disjoint_loop s_1 s_2 i) <==> disjoint_p s_1 s_2))
      (decreases (length s_1 - i))
let rec disjoint_lemma s_1 s_2 i =
   slice_lemma s_1;
   if i < length s_1 then
      let a = index s_1 i in
      if mem a s_2 then
         ()
      else
         disjoint_lemma s_1 s_2 (i + 1)
   else
      ()

val disjoint:
   s_1:seq 'a ->
   s_2:seq 'a ->
   Tot (b:bool{b2t b <==> disjoint_p s_1 s_2})
let disjoint s_1 s_2 =
   disjoint_lemma s_1 s_2 0;
   disjoint_loop s_1 s_2 0
