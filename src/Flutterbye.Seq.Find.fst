(*--build-config
   options:--admit_fsi FStar.Seq;
   other-files:seq.fsi Flutterbye.Seq.Find.fsi
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

module Flutterbye.Seq.Find
   open FStar.Seq

   // todo: this isn't working when used from another module.
   let option_get o =
      match o with
         | Some a ->
            a

   val find__loop:
      s: seq 'a
      -> 'a
      -> i: nat{i <= length s}
      -> c: option nat
      -> Tot (option nat)
         (decreases (length s - i))
   let rec find__loop s a i c =
      if i < length s then
         let c' =
            if is_None c && (a = index s i) then
               Some i
            else
               c in
         find__loop s a (i + 1) c'
      else
         c

   val lemma__basic__loop:
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
            ((is_None (find__loop s a i c) ==>
               (forall j.
                  0 <= j && j < length s ==> index s j <> a))
            /\ (is_Some (find__loop s a i c) ==>
                  ((option_get (find__loop s a i c)) < length s
                  && a = index s (option_get (find__loop s a i c))))))
         (decreases (length s - i))
   let rec lemma__basic__loop s a i c =
      if i < length s then
         let c' =
            if is_None c && a = index s i then
               Some i
            else
               c in
         lemma__basic__loop s a (i + 1) c'
      else
         ()

   let find s a =
      find__loop s a 0 None
   let lemma__basic s a =
      lemma__basic__loop s a 0 None
