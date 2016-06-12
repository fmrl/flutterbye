// $legal:629:
//
// Copyright 2016 Michael Lowell Roberts & Microsoft Research
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
//,$

module Flutterbye.Seq.Map
open FStar.Seq

type mapped_p (#a_t:Type) (#b_t:Type) (f:a_t -> Tot b_t) (s_a: seq a_t) (s_b:seq b_t) =
   b2t (length s_a = length s_b) /\
   (length s_a = 0 \/
      (forall (x:nat).
         x < length s_a ==> f (index s_a x) = index s_b x))

private val map_loop:
   // mapping function
   f:('a -> Tot 'b)
   // input sequence
   -> s:seq 'a
   // accumulator; in this case, the output sequence.
   -> ac:seq 'b{length ac <= length s}
   -> Tot (ac':seq 'b)
      (decreases (length s - length ac))
let rec map_loop f s ac =
   let i = length ac in
   if i < length s then
      let a = index s i in
      let ac' = append ac (create 1 (f a)) in
      map_loop f s ac'
   else
      ac

private val map_lemma:
   f:('a -> Tot 'b)
   -> s:seq 'a
   -> ac:seq 'b{length ac <= length s}
   -> Lemma
      (requires (mapped_p f (slice s 0 (length ac)) ac))
      (ensures (mapped_p f s (map_loop f s ac)))
      (decreases (length s - length ac))
let rec map_lemma f s ac =
   let i = length ac in
   if i < length s then
      let a = index s i in
      let ac' = append ac (create 1 (f a)) in
      map_lemma f s ac'
   else
      ()

// map seq 'a to seq 'b given a function that maps 'a to 'b.
val map:
   f:('a -> Tot 'b) ->
   s:seq 'a ->
   Tot (s':seq 'b{mapped_p f s s'})
let map f s =
   map_lemma f s createEmpty;
   map_loop f s createEmpty
