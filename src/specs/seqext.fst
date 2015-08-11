(*--build-config
   options:--admit_fsi Seq;
   other-files:seq.fsi seqext.fsi
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

module Tesseract.Specs.SeqExt
   open Seq

   val __mem__loop:
      s: seq 'a
      -> i: nat{i < length s}
      -> 'a
      -> bool
      -> Tot bool
         (decreases (length s - i))
   let rec __mem__loop s i a c =
      let z = length s - 1 in
      let c' = c || (a = index s i) in
      if z = i then
         c'
      else
         __mem__loop s (i + 1) a c'

   let mem s a =
      if length s = 0 then
         false
      else
         __mem__loop s 0 a false

   let lemma_mem__mem s a = ()

   val __filter_loop:
      // predicate; if false, then the element is discarded from the sequence.
      ('a -> Tot bool)
      // input sequence
      -> s: seq 'a{length s > 0}
      // index of element being reduced
      -> i: nat{i < length s}
      // accumulator; in this case, the output sequence.
      -> c: seq 'a
      -> Tot (seq 'a)
         (decreases (length s - i))
   let rec __filter_loop p s i c =
      let z = length s - 1 in
      let a = index s i in
      let c' =
         if p a then
            append c (create 1 a)
         else
            c in
      if i = z then
         c'
      else
         __filter_loop p s (i + 1) c'

   let filter p s =
      if length s = 0 then
         createEmpty
      else
         __filter_loop p s 0 createEmpty

   val __lemma_filter_loop__length:
      p: ('a -> Tot bool) ->
      s: seq 'a{length s > 0} ->
      i: nat{i < length s} ->
      c: seq 'a ->
      Lemma
         (requires (length c <= i))
         (ensures (length (__filter_loop p s i c) <= length s))
         (decreases (length s - i))
   let rec __lemma_filter_loop__length p s i c =
      let z = length s - 1 in
      let a = index s i in
      let c' =
         if p a then
            append c (create 1 a)
         else
            c in
      if i = z then
         ()
      else
         __lemma_filter_loop__length p s (i + 1) c'

   let lemma_filter__length p s =
      if length s = 0 then
         ()
      else
         __lemma_filter_loop__length p s 0 createEmpty

   val __lemma_filter__loop__admission:
      p: ('a -> Tot bool)
      -> s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> c: seq 'a
      -> k: nat
      -> Lemma
         (requires (forall j. 0 <= j && j < length c ==> p (index c j)))
         (ensures
            (k < length (__filter_loop p s i c)
            ==> p (index (__filter_loop p s i c) k)))
         (decreases (length s - i))
   let rec __lemma_filter__loop__admission p s i c k =
      let z = length s - 1 in
      let a = index s i in
      let c' =
         if p a then
            append c (create 1 a)
         else
            c in
      if i = z then
         ()
      else
         __lemma_filter__loop__admission p s (i + 1) c' k

   let lemma_filter__admission p s k =
      if length s = 0 then
         ()
      else
         __lemma_filter__loop__admission p s 0 createEmpty k

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
