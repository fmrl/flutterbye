(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi Flutterbye.Seq.Mem;
   other-files:seq.fsi set.fsi Flutterbye.Seq.Mem.fsi Flutterbye.Seq.Unique.fsi
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

module Flutterbye.Seq.Unique
open FStar.Seq
open FStar.Set

// bug: the syntax `type Unique 'a (s:seq 'a) =` doesn't appear to work.
// is it supposed to?
type Unique (#a:Type) (s:seq a) =
   0 = length s
   \/ (forall (i:nat) (j:nat).
         i < length s
         && j < length s
         && index s j = index s i
         ==>
            j == i)

val unique__loop:
   // input sequence
   s:seq 'a
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, a set to track members of the sequence.
   -> c:seq 'a{Unique c}
   -> Tot bool
      (decreases (length s - i))
let rec unique__loop s i c =
   if i < length s then
      let a = index s i in
      if Flutterbye.Seq.Mem.mem a c then
         false
      else
         let c' = append c (create 1 a) in
         unique__loop s (i + 1) c'
   else
      true

let unique s =
   unique__loop s 0 createEmpty

val to_set__loop:
   // input sequence
   s:seq 'a{Unique s}
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, the output set.
   -> c:set 'a
   -> Tot (set 'a)
      (decreases (length s - i))
let rec to_set__loop s i c =
   if i < length s then
      let a = index s i in
      let c' = union c (singleton a) in
      to_set__loop s (i + 1) c'
   else
      c

let to_set s =
   to_set__loop s 0 empty

val lemma__unique__loop:
   // input sequence
   s:seq 'a
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, a set to track members of the sequence.
   -> c:seq 'a{Unique c}
   -> Lemma
      (requires
         (Eq c (slice s 0 i)
         // todo: it seems that length c = i should be implied by the
         // Fstar.Seq.Eq c (FStar.Seq.slice s 0 i) property.
         /\ length c = i))
      (ensures (unique__loop s i c <==> Unique s))
      (decreases (length s - i))
let rec lemma__unique__loop s i c =
   if i < length s then
      let a = index s i in
      if Flutterbye.Seq.Mem.mem a c then
         ()
      else
         let c' = append c (create 1 a) in
         lemma__unique__loop s (i + 1) c'
   else
      ()

let lemma__unique s =
   lemma__unique__loop s 0 createEmpty

let lemma__empty s = ()

type Synonymous (#a:Type) (s_0:seq a{Unique s_0}) (s_1:set a) =
   forall x.
      Flutterbye.Seq.Mem.mem x s_0 <==> mem x s_1

val lemma__to_set__loop:
   // input sequence
   s:seq 'a{Unique s}
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, the output set.
   -> c:set 'a
   -> Lemma
      (requires
         ((i = 0 ==> Equal c empty)
         /\ (Synonymous (slice s 0 i) c)))
      (ensures (Synonymous s (to_set__loop s i c)))
      (decreases (length s - i))
let rec lemma__to_set__loop s i c =
   if i < length s then
      let a = index s i in
      let c' = union c (singleton a) in
      Flutterbye.Seq.Mem.lemma__slice s a;
      assert (Flutterbye.Seq.Mem.mem a (slice s 0 (i + 1)));
      lemma__to_set__loop s (i + 1) c'
   else
      ()

let lemma__to_set s =
   lemma__to_set__loop s 0 empty
