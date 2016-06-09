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

module Flutterbye.Seq.Remove
open FStar.Seq

val remove:
   s:seq 'a{length s > 0}
   -> i:nat{i < length s}
   -> 'a
   -> Tot (seq 'a)
let remove s i a =
   let l = slice s 0 i in
   let r = slice s (i + 1) (length s) in
   append l r

abstract val lemma__length:
   s:seq 'a{length s > 0}
   -> i:nat{i < length s}
   -> a:'a
   -> Lemma
      (requires (True))
      (ensures (length (remove s i a) = length s - 1))
let lemma__length s i a = ()

abstract val lemma__index:
   s:seq 'a{length s > 0}
   -> i:nat{i < length s}
   -> a:'a
   -> Lemma
      (requires (True))
      (ensures
         ((forall (j:nat).
            (j < i) ==> (index (remove s i a) j = index s j))
         /\ (forall (j:nat).
            (i <= j && j < length (remove s i a)) ==>
               (index (remove s i a) j = index s (j + 1)))))
let lemma__index s i a = ()
