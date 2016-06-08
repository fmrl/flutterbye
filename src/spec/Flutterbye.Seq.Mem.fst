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
open Flutterbye.Seq.Find

type mem_t (#a:Type) (x:a) (s:seq a) =
   exists (i:nat).
      i < length s && index s i = x

val mem: x:'a -> s:seq 'a -> Tot (b:bool{b <==> mem_t x s})
let mem a s =
   is_Some (find a s)

val lemma__index:
   s:seq 'a{length s > 0}
   -> i:nat{i < length s}
   -> Lemma
      (requires (True))
      (ensures (mem_t (index s i) s))
let lemma__index s i =
   lemma__find (index s i) s

val lemma__slice_1:
   a:'a
   -> s:seq 'a
   -> Lemma
      (requires (mem_t a s))
      (ensures
         (forall (i:nat) (j:nat) (q:seq 'a).
            ((j < length q /\ i <= j /\ (equal s (slice q i j))) ==>
               mem_t a q)))
let lemma__slice_1 a s =
   ()

// todo: this lemma could be generalized to any slice containing index `i`.
// (would that subsume lemma__slice_1?)
val lemma__slice_2:
   a:'a
   -> s:seq 'a
   -> Lemma
      (requires (mem_t a s))
      (ensures
         (forall (i:nat).
            ((i < length s && index s i = a) ==>
               (mem_t a (slice s 0 (i + 1))))))
let lemma__slice_2 a s =
   ()

private val lemma__append__case_1:
   x:'a
   -> s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires (mem_t x s_1))
      (ensures (mem_t x (append s_1 s_2)))
let lemma__append__case_1 x s_1 s_2 =
   ()

private val lemma__append__case_2:
   x:'a
   -> s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires (mem_t x s_2))
      (ensures (mem_t x (append s_1 s_2)))
let lemma__append__case_2 x s_1 s_2 =
   let s' = append s_1 s_2 in
   let i = length s_1 in
   let j = length s' in
   let s'' = slice s' i j in
   lemma__slice_1 x s'';
   lemma__slice_2 x s''

val lemma__append:
   x:'a
   -> s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires (mem_t x s_1 \/ mem_t x s_2))
      (ensures (mem_t x (append s_1 s_2)))
let lemma__append x s_1 s_2 =
   if mem x s_1 then
      lemma__append__case_1 x s_1 s_2
   else
      lemma__append__case_2 x s_1 s_2

val lemma__empty:
   x:'a
   -> s:seq 'a
   -> Lemma
      (requires (length s = 0))
      (ensures (~ (mem_t x s)))
      [SMTPat (mem x s)]
let lemma__empty x s = ()

val lemma__create:
   n:nat{n > 0}
   -> a:'a
   -> Lemma
      (requires (True))
      (ensures (mem_t a (create n a)))
      [SMTPat (create n a)]
let lemma__create n a =
   let s = create n a in
   assert (index s 0 = a);
   ()
