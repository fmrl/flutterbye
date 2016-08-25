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

module Flutterbye.Linearization
open FStar.Seq
open Flutterbye.Seq
open Flutterbye.Entropy

type transaction_t 'a = 'a -> 'a

type xnid_t (#a_t:Type) (s_xn:seq (transaction_t a_t)) =
   | XnId: as_nat:nat{as_nat < length s_xn} -> xnid_t s_xn

type pending_t (#a_t:Type) (s_xn:seq (transaction_t a_t)) =
   | Pending: id:xnid_t s_xn -> s:a_t -> pending_t s_xn

type step_t (#a_t:Type) (s_xn:seq (transaction_t a_t)) =
   | Next: id:xnid_t s_xn -> step_t s_xn
   | Studder: id:xnid_t s_xn -> step_t s_xn

val linearize_loop:
   s_xn:seq (transaction_t 'a)
   -> a:'a
   -> p:seq (pending_t s_xn)
   -> l:seq (step_t s_xn)
   -> Tot (l':seq (step_t 'a))
      decreases (length p)
let rec linearize_loop s_xn a p l =
   if length p = 0 then
      l
   else
      let i = 0 in
      let xn_p = index p i in
      let xnid = Pending.id xn_p in
      let allow = (Pending.s xn_p = a) in
      if allow
         // step 
      else
         // todo: i'll bet this needs to be two loops!
         let l' = append (create (Studder xnid) 1) in
         let retry = Pending xnid a in
         let p' = append (remove p i) (create retry 1) in
         linearize_loop s_xn a p' l'


      let s' = 
         if allow then
            let f = index s_xn (XnId.as_nat xnid) in
            f s
         else
            s
      in
      let p' = 
         if allow then
            remove p i
         else
            p
      in
      let l' = 
         if allow then
            append (create (Step xnid) 1)
         else
            append (create (Studder xnid) 1)
      in

   
type linearized_p (#a_t:Type) (#b_t:Type) (s_xn:seq (transaction_t a_t)) (s_0:a_t) (l:seq (step_t s_xn)) =
   length s_xn = 0
   \/ // every transaction has a corresponding `Step` operation in
      // the linearization sequence.
      forall (x:xnid_t s_xn).
         (exists (y:nat{y < length l}).
            let op = index l y in
            is_Step op && Step.id op = x)

val linearize:
   s_xn:seq (transaction_t 'a)
   -> s_0:'a
   -> e:entropy_t 'b
   -> Tot (l:seq (step_t 'a)){linearized_p s_xn s_0 l})
let linearize s_xn s_0 =
   let p = 
      map
         (fun i x ->
            Pending i s_0)
         s_xn
   in
   linearize_loop s_xn p createEmpty*)

