(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi Flutterbye.Seq.Mem;
   other-files:seq.fsi Flutterbye.Seq.Mem.fsi
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

// notes: i'm putting this module aside for the moment becasue i've realized
// that sequence intesection is a more complicated concept than i'm really
// interested in tackling for the moment-- mostly that sequence intersection
// should probably mirror multiset intersection.

// todo: in interactive mode, if this module name doesn't match the interface
// module name, it can cause timeouts that are difficult to connect to a simple
// cut-and-paste error.
module Flutterbye.Seq.Intersect
open FStar.Seq
open Flutterbye.Seq.Mem

type Intersect (#a:Type) (s_i:seq a) (s_1:seq a) (s_2:seq a) =
   forall x.
      mem x s_i <==> (mem x s_1 /\ mem x s_2)

let lemma__empty s_1 s_2 = ()

val intersect__loop:
   s_1:seq 'a
   -> s_2:seq 'a
   -> i:nat{i <= length s_1}
   -> a:seq 'a
   -> Tot (seq 'a)
      (decreases (length s_1 - i))
// todo: if the function identifier is misspelled, the error message produced
// is accurate but confusing because of assumptions that the compiler is making
// in interactive mode.
let rec intersect__loop s_1 s_2 i a =
   if i < length s_1 then
      let e_i = index s_1 i in
      if mem e_i s_2 then
         let a' = append a (create 1 e_i) in
         intersect__loop s_1 s_2 (i + 1) a'
      else
         intersect__loop s_1 s_2 (i + 1) a
   else
      a

val lemma__intersect__loop:
   s_1:seq 'a
   -> s_2:seq 'a
   -> i:nat{i <= length s_1}
   -> a:seq 'a
   -> Lemma
      (requires (Intersect a (slice s_1 0 i) s_2))
      (ensures (Intersect (intersect__loop s_1 s_2 i a) s_1 s_2))
      (decreases (length s_1 - i))
// todo: in interactive mode, if the function identifier is misspelled, the
// error message produced is accurate but confusing because of assumptions that
// the compiler is making.
let rec lemma__intersect__loop s_1 s_2 i a =
   // todo: would knowing about length help? intersection <= args.
   if i < length s_1 then
      let e_i = index s_1 i in
      if mem e_i s_2 then
         let a' = append a (create 1 e_i) in
         Flutterbye.Seq.Mem.lemma__append e_i a (create 1 e_i);
         assert (mem e_i a');
         Flutterbye.Seq.Mem.lemma__slice_2 e_i s_1;
         assert (mem e_i (slice s_1 0 (i + 1)));
         if mem e_i a then
            lemma__intersect__loop s_1 s_2 (i + 1) a'
         else
            admit ()//lemma__intersect__loop s_1 s_2 (i + 1) a'
     else
        lemma__intersect__loop s_1 s_2 (i + 1) a // proven
  else
     () // proven

let intersect s_1 s_2 =
   lemma__intersect__loop s_1 s_2 0 createEmpty;
   intersect__loop s_1 s_2
