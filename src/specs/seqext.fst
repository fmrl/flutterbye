(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi Flutterbye.Seq.Find --admit_fsi Flutterbye.Seq.Mem --admit_fsi Flutterbye.Seq.Filter;
   other-files:seq.fsi ../Flutterbye.Seq.Find.fsi ../Flutterbye.Seq.Mem.fsi ../Flutterbye.Seq.Filter.fsi seqext.fsi
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

module Flutterbye.Specs.SeqExt
   open FStar.Seq
   open Flutterbye.Seq.Find
   open Flutterbye.Seq.Mem
   open Flutterbye.Seq.Filter

   let count p s =
      length (filter p s)

   let lemma_count__length p s =
      Flutterbye.Seq.Filter.lemma__length p s

   let insert s i a =
      let l = slice s 0 i in
      let c = create 1 a in
      let r = slice s i (length s) in
      append (append l c) r

   let lemma_insert__length s i a = ()
   let lemma_insert__contents s i a = ()

   let remove s i a =
      let l = slice s 0 i in
      let r = slice s (i + 1) (length s) in
      append l r

   let lemma_remove__length s i a = ()
   let lemma_remove__contents s i a = ()
