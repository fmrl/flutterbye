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

module Flutterbye.Seq.Insert
open FStar.Seq

private type inserted_p (#a_t:Type) (s:seq a_t) (i:nat{i <= length s}) (a:a_t) (s':seq a_t) =
   length s' = length s + 1 /\
   index s' i = a /\
   (forall (x:nat).
      x < i ==> index s' x = index s x) /\
   (forall (x:nat).
      i < x && x < length s' ==>
         index s' x = index s (x - 1)) /\
   (i = 0 ==> equal s' (append (create 1 a) s)) /\
   (i = length s ==> equal s' (append s (create 1 a)))

val insert:
   s:seq 'a
   -> i:nat{i <= length s}
   -> a:'a
   -> Tot (s':seq 'a{inserted_p s i a s'})
let insert s i a =
   let l = slice s 0 i in
   let c = create 1 a in
   let r = slice s i (length s) in
   append (append l c) r