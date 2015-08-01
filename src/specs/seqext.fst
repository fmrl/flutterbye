(*--build-config
   options:--admit_fsi Seq;
   other-files:ext.fst seq.fsi
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

   val __filter_loop:
      // predicate; if false, then the element is discarded from the sequence.
      ('a -> Tot bool)
      // input sequence
      -> s: seq 'a{length s > 0}
      // index of element being reduced
      -> i: nat{i < length s}
      // accumulator; in this case, the output sequence.
      -> b: seq 'a
      -> Tot (seq 'a)
         (decreases (length s - i))
   let rec __filter_loop p s i b =
      let z = length s - 1 in
      let a = index s i in
      let b' =
         if p a then
            append (create 1 a) b
         else
            b in
      if i = z then
         b'
      else
         __filter_loop p s (i + 1) b'

   val filter:
      // predicate; if false, then the element is discarded from the sequence.
      ('a -> Tot bool)
      // input sequence
      -> seq 'a
      // output sequence
      -> Tot (seq 'a)
   let filter p s =
      if length s = 0 then
         createEmpty
      else
         __filter_loop p s 0 createEmpty

   val __lemma_filter_loop__length:
      p: ('a -> Tot bool) ->
      s: seq 'a{length s > 0} ->
      i: nat{i < length s} ->
      b: seq 'a ->
      Lemma
         (requires (length b <= i))
         (ensures (length (__filter_loop p s i b) <= length s))
         (decreases (length s - i))
   let rec __lemma_filter_loop__length p s i b =
      let z = length s - 1 in
      let a = index s i in
      let b' =
         if p a then
            append (create 1 a) b
         else
            b in
      if i = z then
         ()
      else
         __lemma_filter_loop__length p s (i + 1) b'

   val __lemma_filter__length:
      p: ('a -> Tot bool) ->
      s: seq 'a ->
      Lemma
         (requires True)
         (ensures length (filter p s) <= length s)
   let __lemma_filter__length p s =
      if length s = 0 then
         ()
      else
         __lemma_filter_loop__length p s 0 createEmpty

   val __lemma_filter_loop__selection:
      p: ('a -> Tot bool) ->
      s: seq 'a{length s > 0} ->
      i: nat{i < length s} ->
      b: seq 'a ->
      Lemma
         (requires forall j. 0 <= j && j < length b ==> p (index b j))
         (ensures
            forall j.
               0 <= j && j < length (__filter_loop p s i b)
               ==> p (index (__filter_loop p s i b) j))
         (decreases (length s - i))
   let rec __lemma_filter_loop__selection p s i b =
      let z = length s - 1 in
      let a = index s i in
      let b' =
         if p a then
            append (create 1 a) b
         else
            b in
      if i = z then
         ()
      else
         __lemma_filter_loop__selection p s (i + 1) b'

   val __lemma_filter__selection:
      p: ('a -> Tot bool) ->
      s: seq 'a ->
      Lemma
         (requires True)
         (ensures
            forall i.
               0 <= i && i < length (filter p s)
               ==> p (index (filter p s) i))
   let __lemma_filter__selection p s =
      if length s = 0 then
         ()
      else
         __lemma_filter_loop__selection p s 0 createEmpty
