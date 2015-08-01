(*--build-config
   options:--admit_fsi Seq;
   other-files:ext.fst seq.fsi primitives.fst
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
   open Tesseract.Specs.Primitives
   open Seq

   val __filter__recursion:
      a: Type
      -> b: Type
      -> ((a -> Tot bool)
         -> s: seq a{length s > 0}
         -> i: nat{i < length s}
         -> m: seq a
         -> Tot b)
      -> (seq a -> Tot b)
      -> (a -> Tot bool)
      -> s: seq a{length s > 0}
      -> i: nat{i < length s}
      -> m: seq a
      -> Tot b
   let __filter__recursion 'a 'b y w p s i m =
      let z = length s - 1 in
      let a = index s i in
      let m' =
         if p a then
            append (create 1 a) m
         else
            m in
      if i = z then
         w m'
      else
         y p s (i + 1) m'

   val __filter_loop:
      a: Type
      -> (a -> Tot bool)
      -> s: seq a{length s > 0}
      -> i: nat{i < length s}
      -> m: seq a
      -> Tot (seq a)
         (decreases (length s - i))
   let rec __filter__loop 'a (p: ('a -> Tot bool)) (s: seq 'a{length s > 0}) (i: nat{i < length s}) (m: seq 'a) =
      __filter__recursion 'a (seq 'a) (__filter__loop 'a) id

   val filter:
      p: ('a -> Tot bool) ->
      s: seq 'a ->
      Tot (seq 'a)
   let filter p s =
      if length s = 0 then
         createEmpty
      else
         let rec loop = __filter__recursion loop id in
         loop p s 0 createEmpty

   val __lemma_filter_loop__length:
      p: ('a -> Tot bool) ->
      s: seq 'a{length s > 0} ->
      i: nat{i < length s} ->
      m: seq 'a ->
      Lemma
         (requires (length m <= i))
         (ensures (length (__filter__recursion p s i m) <= length s))
         (decreases (length s - i))
   let rec __lemma_filter_loop__length p s i m =
      let z = length s - 1 in
      let a = index s i in
      let m' =
         if p a then
            append (create 1 a) m
         else
            m in
      if i = z then
         ()
      else
         __lemma_filter_loop__length p s (i + 1) m'

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
      m: seq 'a ->
      Lemma
         (requires forall j. 0 <= j && j < length m ==> p (index m j))
         (ensures
            forall j.
               0 <= j && j < length (__filter__recursion p s i m)
               ==> p (index (__filter__recursion p s i m) j))
         (decreases (length s - i))
   let rec __lemma_filter_loop__selection p s i m =
      let z = length s - 1 in
      let a = index s i in
      let m' =
         if p a then
            append (create 1 a) m
         else
            m in
      if i = z then
         ()
      else
         __lemma_filter_loop__selection p s (i + 1) m'

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

   (*val reverse:
      s: seq 'a
      -> Tot (seq 'a)
   let reverse s =
      if length s = 0 then
         createEmpty
      else
         fold_right s (__reverse__foldr s) createEmpty

   val __lemma_involutive__reverse:
      s: seq 'a
      -> Lemma
         (ensures Eq s (reverse (reverse s)))
   let __lemma_involutive__reverse s =
      // todo: prove me.
      admit ()

   val insert:
      s: seq 'a
      -> i: nat{i <= length seq}
      -> 'a
      -> Tot (seq 'a)
   let insert s i a =
      append*)
