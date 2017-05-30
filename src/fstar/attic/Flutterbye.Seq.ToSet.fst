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

module Flutterbye.Seq.ToSet
open FStar.Seq
open FStar.Set

private val to_set_loop:
   s:seq 'a ->
   i:nat{i <= length s} ->
   ac:set 'a ->
   Tot (set 'a)
      (decreases (length s - i))
let rec to_set_loop s i ac =
   if i < length s then
      let a = index s i in
      let ac' = union ac (singleton a) in
      to_set_loop s (i + 1) ac'
   else
      ac

private type from_seq_p (#a:Type) (s:seq a) (s':set a) =
   (length s = 0 /\ FStar.Set.equal s' FStar.Set.empty) \/
   (forall x.
      Flutterbye.Seq.Mem.mem_p x s <==> b2t (mem x s'))

private val to_set_lemma:
   s:seq 'a ->
   i:nat{i <= length s} ->
   ac:set 'a ->
   Lemma
      (requires (from_seq_p (slice s 0 i) ac))
      (ensures (from_seq_p s (to_set_loop s i ac)))
      (decreases (length s - i))
let rec to_set_lemma s i ac =
   Flutterbye.Seq.Mem.slice_lemma s;
   if i < length s then
      let a = index s i in
      let ac' = union ac (singleton a) in
      to_set_lemma s (i + 1) ac'
   else
      ()

val to_set: (s:seq 'a) -> Tot (s':set 'a{from_seq_p s s'})
let to_set s =
   to_set_lemma s 0 empty;
   to_set_loop s 0 empty
