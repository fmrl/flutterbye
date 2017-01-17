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

module Flutterbye.Seq.Contains
open FStar.Seq
open Flutterbye.Option
open Flutterbye.Seq.Find
open Flutterbye.Seq.Remove

type contains_p = found_p
let contains = found

abstract val index_lemma:
      #t:Type
   -> s:seq t
   -> i:nat{i < length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (
         (b2t (f (index s i)) ==> contains_p f s)
         /\ (~ (contains_p f s) ==> b2t (not (f (index s i))))
      ))
let index_lemma #t s i f =
   ()

abstract val append_lemma:
      #t:Type
   -> s_1:seq t
   -> s_2:seq t
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (
         (contains_p f s_1 \/ contains_p f s_2)
         <==> contains_p f (append s_1 s_2)
      ))
let append_lemma #t s_1 s_2 f =
   Flutterbye.Seq.Find.append_lemma s_1 s_2

abstract val slice_lemma:
      #t:Type
   -> s:seq t
   -> i:nat
   -> j:nat{i <= j && j <= length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (
         (contains_p f (slice s i j) ==> contains_p f s)
         /\ (~ (contains_p f s) ==> ~ (contains_p f (slice s i j)))
         /\ (
            ~ (contains_p f (slice s i j))
            ==> (
                ~ (contains_p f s)
                \/ (contains_p f (slice s 0 i))
                \/ (contains_p f (slice s j (length s)))
            )
         )
      ))
let slice_lemma #t s i j f =
   if contains f (slice s i j) then
      ()
   else begin
      if contains f s then begin
         if contains f (slice s 0 i) then
            ()
         else begin
            let s_1 = slice s 0 i in
            let s_2 = slice s i j in
            let s_3 = append s_1 s_2 in
            append_lemma s_1 s_2 f;
            assert (equal s_3 (slice s 0 j));
            assert (~ (contains_p f (slice s 0 j)));
            let s_4 = (slice s j (length s)) in
            let s_5 = append s_3 s_4 in
            append_lemma s_3 s_4 f;
            assert (equal s_5 s);
            assert (contains_p f (slice s j (length s)))
         end
      end
      else
         ()
   end

abstract val create_lemma:
      #t:Type
   -> n:nat
   -> x:t
   -> f:(t -> Tot bool)
   -> Lemma
      (ensures (
         (b2t (n = 0) ==> ~ (contains_p f (create n x)))
         /\ (b2t (n > 0) ==> (b2t (f x) <==> contains_p f (create n x)))
      ))
let create_lemma #t n x f =
   Flutterbye.Seq.Find.create_lemma n x f

val remove_lemma:
      #t:Type{hasEq t}
   -> s:seq t{length s > 0}
   -> i:nat{i < length s}
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (
         (~ (contains_p f s) ==> ~ (contains_p f (remove s i)))
         /\ (
            (contains_p f s /\ get (find f s) <> i)
            ==> contains_p f (remove s i)
         )
      ))
let remove_lemma #t s i f =
   Flutterbye.Seq.Find.remove_lemma s i f
