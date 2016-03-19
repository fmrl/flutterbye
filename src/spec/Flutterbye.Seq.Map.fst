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

module Flutterbye.Seq.Map
open FStar.Seq

private val map__loop:
   // mapping function
   ('a -> Tot 'b)
   // input sequence
   -> s:seq 'a
   // accumulator; in this case, the output sequence.
   -> c:seq 'b{length c <= length s}
   -> Tot (seq 'b)
      (decreases (length s - length c))
let rec map__loop f s c =
   let i = length c in
   if i < length s then
      let a = index s i in
      let c' = append c (create 1 (f a)) in
      map__loop f s c'
   else
      c

private val lemma__length__loop:
   f:('a -> Tot 'b)
   -> s:seq 'a
   -> c:seq 'b{length c <= length s}
   -> Lemma
      (requires (True))
      (ensures (length (map__loop f s c) = length s))
      (decreases (length s - length c))
let rec lemma__length__loop f s c =
   let i = length c in
   if i < length s then
      let a = index s i in
      let c' = append c (create 1 (f a)) in
      lemma__length__loop f s c'
   else
      ()

private val lemma__index__loop:
   f:('a -> Tot 'b)
   -> s:seq 'a
   -> c:seq 'b{length c <= length s}
   -> Lemma
      (requires ((forall i. 0 <= i && i < length c ==> index c i = f (index s i))))
      (ensures
         (forall i.
            0 <= i
            && i < length (map__loop f s c)
            ==>
               (i < length s
               && index (map__loop f s c) i = f (index s i))))
      (decreases (length s - length c))
let rec lemma__index__loop f s c =
   let i = length c in
   if i < length s then
      let a = index s i in
      let c' = append c (create 1 (f a)) in
      lemma__index__loop f s c'
   else
      ()

// map seq 'a to seq 'b given a function that maps 'a to 'b.
val map: ('a -> Tot 'b) -> s: seq 'a -> Tot (seq 'b)
let map f s =
   map__loop f s createEmpty

val lemma__length:
   f:('a -> Tot 'b)
   -> s:seq 'a
   -> Lemma
      (requires (True))
      (ensures (length (map f s) = length s))
      [SMTPat (length (map f s))]
let lemma__length f s =
   lemma__length__loop f s createEmpty

val lemma__index:
   f:('a -> Tot 'b)
   -> s:seq 'a
   -> i:nat{i < length s}
   -> Lemma
      (requires (True))
      (ensures (index (map f s) i = f (index s i)))
      [SMTPat (index (map f s) i)]
let lemma__index f s i =
   lemma__index__loop f s createEmpty
