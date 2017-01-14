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

module Flutterbye.Seq.Filter
open FStar.Seq
open Flutterbye.Seq.Contains

// the output sequence will not be longer than the input sequence.
private type never_emits_longer_p (#t:Type) (s:seq t) (s':seq t) =
   b2t (length s' <= length s)

// the output sequence is empty iff no element of `s` satisfies `f`.
private type emits_empty_p
   (#t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
   (s':seq t)
=
   ~ (contains_p f s) <==> b2t (length s' = 0)

// the output sequence must be shorter than the input sequence iff
// at least one element doesn't satisfy `f`.
private type emits_subset_p
   (#t:Type)
   (f:(t -> Tot bool))
   (s:seq t)
   (s':seq t)
=
   contains_p (fun x -> not (f x)) s <==> b2t (length s' < length s)

// the output sequence only contains elements that satisfy `f`.
private type emits_satisfying_p 
   (#a_t:Type) 
   (f:(a_t -> Tot bool)) 
   (s':seq a_t)
=
   forall (i:nat{i < length s'}).
      f (index s' i)

type filter_p (#t:Type) (f:(t -> Tot bool)) (s:seq t) (s':seq t) =
      never_emits_longer_p s s'
   /\ emits_empty_p f s s'
   /\ emits_subset_p f s s'
   /\ emits_satisfying_p f s'

private val filter_loop:
      t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> i:nat{i <= length s}
   -> accum:seq t{filter_p f (slice s 0 i) accum}
   -> Tot (s':seq t{filter_p f s s'})
      (decreases (length s - i))
let rec filter_loop t f s i accum =
   let s_0 = slice s 0 i in
   if i = length s then begin
      assert (equal s s_0);
      accum
   end
   else begin
      let s_1 = slice s 0 (i + 1) in
      assert (equal s_0 (slice s_1 0 i));
      let x = index s i in
      if f x then begin
         let accum' = append accum (create 1 x) in
         assert (b2t (f (index s_1 i)));
         Flutterbye.Seq.Contains.slice_lemma s_1 0 i (fun x -> not (f x));
         assert (
                contains_p (fun x -> not (f x)) s_0 
            ==> contains_p (fun x -> not (f x)) s_1
         );
         assert (
                ~ (contains_p (fun x -> not (f x)) s_0) 
            ==> ~ (contains_p (fun x -> not (f x)) s_1)
         );
         assert (filter_p f s_1 accum');
         filter_loop t f s (i + 1) accum'
      end
      else begin
         assert (b2t (not (f (index s_1 i))));
         Flutterbye.Seq.Contains.slice_lemma s_1 0 i f;
         assert (contains_p f s_0 ==> contains_p f s_1);
         assert (~ (contains_p f s_0) ==> ~ (contains_p f s_1));
         assert (filter_p f s_1 accum);
         filter_loop t f s (i + 1) accum
      end
   end

val filter:
      #t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> Tot (s':seq t{filter_p f s s'})
let filter #t f s =
   filter_loop t f s 0 createEmpty
