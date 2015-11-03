(*--build-config
   options:--admit_fsi FStar.Seq;
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

module Flutterbye.Specs.SeqExt
   open FStar.Seq

   // todo: this isn't working when used from Alt.Option
   let option_get o =
      match o with
         | Some a ->
            a

   val __map__loop:
      // mapping function
      ('a -> Tot 'b)
      // input sequence
      -> s: seq 'a
      // accumulator; in this case, the output sequence.
      -> c: seq 'b{length c <= length s}
      -> Tot (seq 'b)
         (decreases (length s - length c))
   let rec __map__loop f s c =
      let i = length c in
      if i < length s then
         let a = index s i in
         let c' = append c (create 1 (f a)) in
         __map__loop f s c'
      else
         c

   val __lemma_map__loop__length:
      f: ('a -> Tot 'b)
      -> s: seq 'a
      -> c: seq 'b{length c <= length s}
      -> Lemma
         (requires (True))
         (ensures (length (__map__loop f s c) = length s))
         (decreases (length s - length c))
   let rec __lemma_map__loop__length f s c =
      let i = length c in
      if i < length s then
         let a = index s i in
         let c' = append c (create 1 (f a)) in
         __lemma_map__loop__length f s c'
      else
         ()

   val __lemma_map__loop__map:
      f: ('a -> Tot 'b)
      -> s: seq 'a
      -> c: seq 'b{length c <= length s}
      -> Lemma
         (requires ((forall i. 0 <= i && i < length c ==> index c i = f (index s i))))
         (ensures
            (forall i.
               0 <= i
               && i < length (__map__loop f s c)
               ==>
                  (i < length s
                  && index (__map__loop f s c) i = f (index s i))))
         (decreases (length s - length c))
   let rec __lemma_map__loop__map f s c =
      let i = length c in
      if i < length s then
         let a = index s i in
         let c' = append c (create 1 (f a)) in
         __lemma_map__loop__map f s c'
      else
         ()

   let map f s =
      __map__loop f s createEmpty
   let lemma_map__length f s =
      __lemma_map__loop__length f s createEmpty
   let lemma_map__map f s i =
      __lemma_map__loop__map f s createEmpty

   val __find__loop:
      s: seq 'a
      -> 'a
      -> i: nat{i <= length s}
      -> c: option nat
      -> Tot (c': option nat)
         (decreases (length s - i))
   let rec __find__loop s a i c =
      if i < length s then
         let c' =
            if is_None c && (a = index s i) then
               Some i
            else
               c in
         __find__loop s a (i + 1) c'
      else
         c

   val __lemma_find__index__loop:
      s: seq 'a
      -> a: 'a
      -> i: nat{i <= length s}
      -> c: option nat
      -> Lemma
         (requires
            ((is_None c ==>
               (forall j.
                  0 <= j && j < i ==> index s j <> a))
            /\ (is_Some c ==>
                  ((option_get c) < length s
                  && a = index s (option_get c)))))
         (ensures
            ((is_None (__find__loop s a i c) ==>
               (forall j.
                  0 <= j && j < length s ==> index s j <> a))
            /\ (is_Some (__find__loop s a i c) ==>
                  ((option_get (__find__loop s a i c)) < length s
                  && a = index s (option_get (__find__loop s a i c))))))
         (decreases (length s - i))
   let rec __lemma_find__index__loop s a i c =
      if i < length s then
         let c' =
            if is_None c && a = index s i then
               Some i
            else
               c in
         __lemma_find__index__loop s a (i + 1) c'
      else
         ()

   let find s a =
      __find__loop s a 0 None
   let lemma_find__index s a =
      __lemma_find__index__loop s a 0 None

   let mem s a =
      is_Some (find s a)
   let lemma_mem__mem s a =
      ()

   let lemma_mem__index s i =
      __lemma_find__index__loop s (index s i) 0 None

   let lemma_mem__slice s0 a s1 j i =
      ()

   val __lemma_mem__append1:
      s0: seq 'a
      -> s1: seq 'a
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (mem s0 a ==> mem (append s0 s1) a))
   let __lemma_mem__append1 s0 s1 a =
      ()

   val __lemma_mem__append2:
      s0: seq 'a
      -> s1: seq 'a
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (mem s1 a ==> mem (append s0 s1) a))
   let __lemma_mem__append2 s0 s1 a =
      if mem s1 a then
         let s' = append s0 s1 in
         let i = length s0 in
         let j = length s' in
         let s1' = slice s' i j in
         lemma_mem__slice s1' a s' j i
      else
         ()

   let lemma_mem__append s0 s1 a =
      __lemma_mem__append1 s0 s1 a;
      __lemma_mem__append2 s0 s1 a

   val __filter__loop:
      // predicate; if false, then the element is discarded from the sequence.
      ('a -> Tot bool)
      // input sequence
      -> s: seq 'a
      // index of element being reduced with (length s) as representing
      // the base case.
      -> i: nat{i <= length s}
      // accumulator; in this case, the output sequence.
      -> c: seq 'a
      -> Tot (seq 'a)
         (decreases (length s - i))
   let rec __filter__loop p s i c =
      if i = length s then
         c
      else
         let a = index s i in
         let c' =
            if p a then
               append c (create 1 a)
            else
               c in
         __filter__loop p s (i + 1) c'

   let filter p s =
      __filter__loop p s 0 createEmpty

   val __lemma_filter__loop__length:
      p: ('a -> Tot bool) ->
      s: seq 'a ->
      i: nat{i <= length s} ->
      c: seq 'a ->
      Lemma
         (requires (length c <= i))
         (ensures (length (__filter__loop p s i c) <= length s))
         (decreases (length s - i))
   let rec __lemma_filter__loop__length p s i c =
      if i = length s then
         ()
      else
         let a = index s i in
         let c' =
            if p a then
               append c (create 1 a)
            else
               c in
         __lemma_filter__loop__length p s (i + 1) c'

   val lemma_filter__length:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> Lemma
         (requires (True))
         (ensures (length (filter p s) <= length s))
         [SMTPat (length (filter p s))]
   let lemma_filter__length p s =
      __lemma_filter__loop__length p s 0 createEmpty

   val __lemma_filter__loop__admission:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> i: nat{i <= length s}
      // accumulator-- in this case, a filtered sequence being constructed.
      -> c: seq 'a
      // free variable (forall)
      -> j: nat
      -> Lemma
         (requires
            (forall k.
               0 <= k && k < length c ==> p (index c k)))
         (ensures
            (j < length (__filter__loop p s i c)
            ==> p (index (__filter__loop p s i c) j)))
         (decreases (length s - i))
   let rec __lemma_filter__loop__admission p s i c j =
      if i = length s then
         ()
      else
         let a = index s i in
         let c' =
            if p a then
               append c (create 1 a)
            else
               c in
         __lemma_filter__loop__admission p s (i + 1) c' j

   let lemma_filter__admission p s i =
      __lemma_filter__loop__admission p s 0 createEmpty i

   val __lemma_filter__loop__mem:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> i: nat{i <= length s}
      -> c: seq 'a
      -> Lemma
         (requires
            (forall j.
               (0 <= j && j < length c) ==> (mem s (index c j))))
         (ensures
            (forall j.
               (0 <= j && j < length (__filter__loop p s i c)) ==> (mem s (index (__filter__loop p s i c) j))))
         (decreases (length s - i))
   let rec __lemma_filter__loop__mem p s i c =
      if i = length s then
         ()
      else
         let a = index s i in
         let c' =
            if p a then
               append c (create 1 a)
            else
               c in
         __lemma_filter__loop__mem p s (i + 1) c'

   let lemma_filter__mem p s =
      __lemma_filter__loop__mem p s 0 createEmpty

   let count p s =
      length (filter p s)

   let lemma_count__length p s =
      lemma_filter__length p s

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
