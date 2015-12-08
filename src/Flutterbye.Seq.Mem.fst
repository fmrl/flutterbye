(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi Flutterbye.Seq.Find;
   other-files:seq.fsi Flutterbye.Seq.Find.fsi Flutterbye.Seq.Mem.fsi
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

module Flutterbye.Seq.Mem
open FStar.Seq
open Flutterbye.Seq.Find

let mem a s =
   is_Some (find a s)

let lemma__mem a s =
   ()

let lemma__index s i =
   lemma__find (index s i) s

let lemma__slice_1 a s =
   ()

let lemma__slice_2 a s =
   ()

val lemma__append__case_1:
   x:'a
   -> s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires (mem x s_1))
      (ensures (mem x (append s_1 s_2)))
let lemma__append__case_1 x s_1 s_2 =
   ()

val lemma__append__case_2:
   x:'a
   -> s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires (mem x s_2))
      (ensures (mem x (append s_1 s_2)))
let lemma__append__case_2 x s_1 s_2 =
   let s' = append s_1 s_2 in
   let i = length s_1 in
   let j = length s' in
   let s'' = slice s' i j in
   lemma__slice_1 x s'';
   lemma__slice_2 x s''

let lemma__append x s_1 s_2 =
   if mem x s_1 then
      lemma__append__case_1 x s_1 s_2
   else
      lemma__append__case_2 x s_1 s_2
