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

val lemma__append__case1:
   a:'a
   -> s0:seq 'a
   -> s1:seq 'a
   -> Lemma
      (requires (True))
      (ensures (mem a s0 ==> mem a (append s0 s1)))
let lemma__append__case1 a s0 s1 =
   ()

val lemma__append__case2:
   a:'a
   -> s0:seq 'a
   -> s1:seq 'a
   -> Lemma
      (requires (True))
      (ensures (mem a s1 ==> mem a (append s0 s1)))
let lemma__append__case2 a s0 s1 =
   if mem a s1 then
      let s' = append s0 s1 in
      let i = length s0 in
      let j = length s' in
      let s1' = slice s' i j in
      lemma__slice_1 a s1';
      lemma__slice_2 a s1'
   else
      ()

let lemma_mem__append a s0 s1 =
   lemma__append__case1 a s0 s1;
   lemma__append__case2 a s0 s1
