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

   let mem s a =
      is_Some (find s a)

   let lemma__basic s a =
      ()

   let lemma__index s i =
      Flutterbye.Seq.Find.lemma__basic s (index s i)

   let lemma__slice s0 a s1 j i =
      ()

   val lemma__append__case1:
      s0: seq 'a
      -> s1: seq 'a
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (mem s0 a ==> mem (append s0 s1) a))
   let lemma__append__case1 s0 s1 a =
      ()

   val lemma__append__case2:
      s0: seq 'a
      -> s1: seq 'a
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (mem s1 a ==> mem (append s0 s1) a))
   let lemma__append__case2 s0 s1 a =
      if mem s1 a then
         let s' = append s0 s1 in
         let i = length s0 in
         let j = length s' in
         let s1' = slice s' i j in
         lemma__slice s1' a s' j i
      else
         ()

   let lemma_mem__append s0 s1 a =
      lemma__append__case1 s0 s1 a;
      lemma__append__case2 s0 s1 a
