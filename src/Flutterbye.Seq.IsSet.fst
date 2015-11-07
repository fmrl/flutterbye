(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi Flutterbye.Seq.Mem;
   other-files:seq.fsi Flutterbye.Seq.IsSet.fsi Flutterbye.Seq.Mem.fsi
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

module Flutterbye.Seq.IsSet
   open FStar.Seq
   open Flutterbye.Seq.Mem

   // bug: the syntax `type IsSet 'a (s:seq 'a) =` doesn't appear to work.
   // is it supposed to?
   type IsSet (#a:Type) (s:seq a) =
      0 = length s
      \/ (forall (i:nat) (j:nat).
            i < length s
            && j < length s
            && index s j = index s i
            ==>
               j == i)

   val is_set__loop:
      // input sequence
      s: seq 'a
      // index of element being examined
      -> i: nat{i <= length s}
      // accumulator; in this case, a set to track members of the sequence.
      -> c: seq 'a{IsSet c}
      -> Tot bool
         (decreases (length s - i))
   let rec is_set__loop s i c =
      if i < length s then
         let a = index s i in
         if mem a c then
            false
         else
            let c' = append c (create 1 a) in
            is_set__loop s (i + 1) c'
      else
         true

   let is_set s =
      is_set__loop s 0 createEmpty

   val lemma__basic__loop:
      // input sequence
      s:seq 'a
      // index of element being examined
      -> i:nat{i <= length s}
      // accumulator; in this case, a set to track members of the sequence.
      -> c:seq 'a{IsSet c}
      -> Lemma
         (requires
            (Eq c (slice s 0 i)
            /\ length c = i))
               // todo: it seems that length c = i should be implied by the
               // Eq c (slice s 0 i) property.
         (ensures (is_set__loop s i c <==> IsSet s))
         (decreases (length s - i))
   let rec lemma__basic__loop s i c =
      if i < length s then
         let a = index s i in
         if mem a c then
            ()
         else
            let c' = append c (create 1 a) in
            lemma__basic__loop s (i + 1) c'
      else
         ()

   let lemma__basic s =
      lemma__basic__loop s 0 createEmpty
