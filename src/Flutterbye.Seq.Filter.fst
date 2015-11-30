(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi Flutterbye.Seq.Mem;
   other-files:seq.fsi Flutterbye.Seq.Mem.fsi Flutterbye.Seq.Filter.fsi
--*)

// $legal:614:
//
// Copyright 2015 Michael Lowell Roberts
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
// ,$

module Flutterbye.Seq.Filter
open FStar.Seq
open Flutterbye.Seq.Mem

val filter__loop:
   // predicate; if false, then the element is discarded from the sequence.
   ('a -> Tot bool)
   // input sequence
   -> s:seq 'a
   // index of element being reduced with (length s) as representing
   // the base case.
   -> i:nat{i <= length s}
   // accumulator; in this case, the output sequence.
   -> c:seq 'a
   -> Tot (seq 'a)
      (decreases (length s - i))
let rec filter__loop p s i c =
   if i = length s then
      c
   else
      let a = index s i in
      let c' =
         if p a then
            append c (create 1 a)
         else
            c in
      filter__loop p s (i + 1) c'

let filter p s =
   filter__loop p s 0 createEmpty

val lemma__length__loop:
   p: ('a -> Tot bool)
   -> s:seq 'a
   -> i:nat{i <= length s}
   -> c:seq 'a
   -> Lemma
      (requires (length c <= i))
      (ensures (length (filter__loop p s i c) <= length s))
      (decreases (length s - i))
let rec lemma__length__loop p s i c =
   if i = length s then
      ()
   else
      let a = index s i in
      let c' =
         if p a then
            append c (create 1 a)
         else
            c in
      lemma__length__loop p s (i + 1) c'

let lemma__length p s =
   lemma__length__loop p s 0 createEmpty

val lemma__predicate__loop:
   p: ('a -> Tot bool)
   -> s:seq 'a
   -> i:nat{i <= length s}
   // accumulator-- in this case, a filtered sequence being constructed.
   -> c:seq 'a
   // free variable (forall)
   -> j:nat
   -> Lemma
      (requires
         (forall k.
            0 <= k && k < length c ==> p (index c k)))
      (ensures
         (j < length (filter__loop p s i c)
         ==> p (index (filter__loop p s i c) j)))
      (decreases (length s - i))
let rec lemma__predicate__loop p s i c j =
   if i = length s then
      ()
   else
      let a = index s i in
      let c' =
         if p a then
            append c (create 1 a)
         else
            c in
      lemma__predicate__loop p s (i + 1) c' j

let lemma__predicate p s i =
   lemma__predicate__loop p s 0 createEmpty i

val lemma__mem__loop:
   p: ('a -> Tot bool)
   -> s:seq 'a
   -> i:nat{i <= length s}
   -> c:seq 'a
   -> Lemma
      (requires
         (forall (j:nat).
            (j < length c) ==> (mem (index c j) s)))
      (ensures
         (forall (j:nat).
            (j < length (filter__loop p s i c)) ==>
               (mem (index (filter__loop p s i c) j) s)))
      (decreases (length s - i))
let rec lemma__mem__loop p s i c =
   if i = length s then
      ()
   else
      let a = index s i in
      let c' =
         if p a then
            append c (create 1 a)
         else
            c in
      lemma__mem__loop p s (i + 1) c'

let lemma__mem p s =
   lemma__mem__loop p s 0 createEmpty
