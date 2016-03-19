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
val option_get: o:option 'a{is_Some o} -> Tot 'a
let option_get o =
   match o with
      | Some a ->
         a

private val find__loop:
   'a
   -> s:seq 'a
   -> i:nat{i <= length s}
   -> c:(option nat)
   -> Tot (option nat)
      (decreases (length s - i))
let rec find__loop a s i c =
   if i < length s then
      let c' =
         if is_None c && (a = index s i) then
            Some i
         else
            c in
      find__loop a s (i + 1) c'
   else
      c

private val lemma__find__loop:
   a:'a
   -> s:seq 'a
   -> i:nat{i <= length s}
   -> c:(option nat)
   -> Lemma
      (requires
         ((is_None c ==>
            (forall (j:nat).
               (j < i) ==> (index s j <> a)))
         /\ (is_Some c ==>
               ((option_get c) < length s
               && a = index s (option_get c)))))
      (ensures
         ((is_None (find__loop a s i c) ==>
            (forall (j:nat).
               (j < length s) ==> (index s j <> a)))
         /\ (is_Some (find__loop a s i c) ==>
               ((option_get (find__loop a s i c)) < length s
               && a = index s (option_get (find__loop a s i c))))))
      (decreases (length s - i))
let rec lemma__find__loop a s i c =
   if i < length s then
      let c' =
         if is_None c && a = index s i then
            Some i
         else
            c in
      lemma__find__loop a s (i + 1) c'
   else
      ()

// todo: this should accept an 'a -> bool rather than an 'a.
val find: a:'a -> s:seq 'a -> Tot (option nat)
let find a s =
   find__loop a s 0 None

// todo: can this be broken down into an aggregation of simpler forms?
val lemma__find:
   a:'a
   -> s:seq 'a
   -> Lemma
      (requires (True))
      (ensures
         ((is_None (find a s) ==>
            (forall (j:nat).
               (j < length s) ==> (index s j <> a)))
         /\ ((is_Some (find a s)) ==>
               ((option_get (find a s) < length s
               && a = index s (option_get (find a s)))))))
      [SMTPat (find a s)]
let lemma__find a s =
   lemma__find__loop a s 0 None
