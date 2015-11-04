(*--build-config
   options:--admit_fsi FStar.Seq;
   other-files:seq.fsi Flutterbye.Seq.Map.fsi
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

module Flutterbye.Seq.Map
   open FStar.Seq

   val map__loop:
      // mapping function
      ('a -> Tot 'b)
      // input sequence
      -> s: seq 'a
      // accumulator; in this case, the output sequence.
      -> c: seq 'b{length c <= length s}
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

   val lemma__preserves_length__loop:
      f: ('a -> Tot 'b)
      -> s: seq 'a
      -> c: seq 'b{length c <= length s}
      -> Lemma
         (requires (True))
         (ensures (length (map__loop f s c) = length s))
         (decreases (length s - length c))
   let rec lemma__preserves_length__loop f s c =
      let i = length c in
      if i < length s then
         let a = index s i in
         let c' = append c (create 1 (f a)) in
         lemma__preserves_length__loop f s c'
      else
         ()

   val lemma__mapping_of_elements__loop:
      f: ('a -> Tot 'b)
      -> s: seq 'a
      -> c: seq 'b{length c <= length s}
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
   let rec lemma__mapping_of_elements__loop f s c =
      let i = length c in
      if i < length s then
         let a = index s i in
         let c' = append c (create 1 (f a)) in
         lemma__mapping_of_elements__loop f s c'
      else
         ()

   let map f s =
      map__loop f s createEmpty
   let lemma__preserves_length f s =
      lemma__preserves_length__loop f s createEmpty
   let lemma__mapping_of_elements f s i =
      lemma__mapping_of_elements__loop f s createEmpty
