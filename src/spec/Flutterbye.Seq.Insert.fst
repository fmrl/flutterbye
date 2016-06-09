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

val insert:
   s:seq 'a
   -> i:nat{i <= length s}
   -> 'a
   -> Tot (seq 'a)
let insert s i a =
   let l = slice s 0 i in
   let c = create 1 a in
   let r = slice s i (length s) in
   append (append l c) r

abstract val lemma__length:
   s: seq 'a
   -> i: nat{i <= length s}
   -> a: 'a
   -> Lemma
      (requires (True))
      (ensures (length (insert s i a) = length s + 1))
      [SMTPat (length (insert s i a))]
let lemma__length s i a = ()

abstract val lemma__index:
   s: seq 'a
   -> i: nat{i <= length s}
   -> a: 'a
   -> Lemma
      (requires (True))
      (ensures
         ((index (insert s i a) i = a)
         /\ (forall (j:nat).
               (j < i) ==> (index (insert s i a) j = index s j))
         /\ (forall (j:nat).
               (i < j && j < length (insert s i a)) ==>
                  (index (insert s i a) j = index s (j - 1)))))
let lemma__index s i a = ()

abstract val lemma__append:
   s: seq 'a
   -> i: nat{i <= length s}
   -> a: 'a
   -> Lemma
      (requires (True))
      (ensures
         (((i = 0) <==> (equal (insert s 0 a) (append (create 1 a) s)))
         /\ ((i = length s) <==>
               (equal (insert s (length s) a) (append s (create 1 a))))))
// todo: eliminate admission.
let lemma__append s i a =
   admit ()
