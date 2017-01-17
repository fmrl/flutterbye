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

// bug: an unmatched (* will not be reported properly by f*.

val remove:
   #t:Type{hasEq t}
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> Tot (s':seq t{length s' = length s - 1})
let remove #t s i =
   let l = slice s 0 i in
   let r = slice s (i + 1) (length s) in
   append l r

val index_lemma:
   #t:Type{hasEq t}
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> Lemma
      (requires (True))
      (ensures
         (  // todo: let_t s' = remove s i
            (forall (x:nat).
               x < i ==> index (remove s i) x = index s x)
         /\ (forall (x:nat).
               i < x && x < length (remove s i) ==> index (remove s i) x = index s (x + 1))
         )
      )
let index_lemma #t s i =
   ()

val equal_lemma:
   #t:Type{hasEq t}
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> Lemma
      (requires (True))
      (ensures
         (  (equal (slice s 0 i) (slice (remove s i) 0 i))
         /\ (equal (slice s (i + 1) (length s)) (slice (remove s i) i (length s - 1)))
         )
      )
let equal_lemma #t s i =
   ()

