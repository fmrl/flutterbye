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

type transaction_t 'a = 'a -> Tot 'a

type pending_t (#a_t:Type) (xns:seq (transaction_t a_t)) =
   | Pending: id:xnid_t xns -> s:a_t -> pending_t xns

type step_t (#a_t:Type) (xns:seq (transaction_t a_t)) =
   | Next: id:xnid_t xns -> step_t xns
   | Studder: id:xnid_t xns -> step_t xns

type has_next_step_p: 
   #a_t:Type 
   -> xns:seq (transaction_t a_t)
   -> steps:seq (step_t xns)      
   -> Type
= fun #a_t xns steps ->
      exists (x:nat{x < length steps}).
         is_Next (index steps x)

type has_fresh_pending_p: 
   #a_t:Type 
   -> xns:seq (transaction_t a_t)
   -> pending:seq (pending_t xns)
   -> state:a_t      
   -> Type
= fun #a_t xns pending state ->
      exists (x:nat{x < length pending}).
         Pending.s (index pending x) = state

type next_loop_p: 
   #a_t:Type 
   -> xns:seq (transaction_t a_t)
   -> pending0:seq (pending_t xns)
   -> state:a_t                                       
   -> pending:seq (pending_t xns)
   -> steps:seq (step_t xns)      
   -> Type
= fun #a_t xns pending0 state pending steps ->
      (length pending0 <= length xns)
      /\ (length pending <= length pending0)
      /\ (has_next_step_p xns steps
         \/ has_fresh_pending_p xns pending state)

val next_loop:
   xns:seq (transaction_t 'a)
   -> pending0:seq (pending_t xns)
   -> state:'a
   -> pending:seq (pending_t xns)
   -> steps:seq (step_t xns)
   -> Tot (steps':seq (step_t xns))
      (decreases (length pending))
let rec next_loop xns pending0 state pending steps =
   if 0 = length pending then
      steps
   else begin
      let i = 0 in
      let p = index pending i in
      let id = Pending.id p in
      let commitable = (Pending.s p = state) in
      let step' =
         if commitable then
            Next id
         else
            Studder id
      in
      let state' =
         if commitable then
            let f = index xns (XnId.as_nat id) in
            f state
         else
           state
      in
      let steps' = append steps (create 1 step') in
      let pending' = remove pending i in
      next_loop xns pending0 state' pending' steps'
   end

val next_loop_lemma:
   xns:seq (transaction_t 'a)
   -> pending0:seq (pending_t xns){length pending <= xns}
   -> state:'a
   -> pending:seq (pending_t xns)
   -> steps:seq (step_t xns)
   -> Lemma 
      (requires (next_loop_p xns pending0 state pending steps))
      (ensures (next_loop_p xns pending0 state createEmpty (next_loop xns pending0 state pending steps))) 
      (decreases (length pending))
let rec next_loop_lemma xns pending0 state pending steps =
   if 0 = length pending then
      ()
   else begin
      let i = 0 in
      let p = index pending i in
      let id = Pending.id p in
      let commitable = (Pending.s p = state) in
      let step' =
         if commitable then
            Next id
         else
            Studder id
      in
      let state' =
         if commitable then
            let f = index xns (XnId.as_nat id) in
            f state
         else
           state
      in
      let steps' = append steps (create 1 step') in
      let pending' = remove pending i in
      next_loop_lemma xns pending0 state' pending' steps'
   end

type next_p: 
   #a_t:Type 
   -> xns:seq (transaction_t a_t)
   -> pending:seq (pending_t xns)
   -> state:a_t
   -> steps:seq (step_t xns)
   -> Type
=
   fun #a_t xns pending state steps ->
      length pending <= length xns

val next:
   xns:seq (transaction_t 'a)
   -> state:'a
   // todo: eliminiate need for `has_fresh_pending_p`.
   -> pending:seq (pending_t xns){length pending <= length xns /\ has_fresh_pending_p xns pending state}
   -> Tot (steps:seq (step_t xns){next_p xns pending state steps})
let next xns state pending =
   next_loop_lemma xns pending state pending createEmpty;
   next_loop xns pending state pending createEmpty

(*type linearized_p (#a_t:Type) (#b_t:Type) (todo:seq (transaction_t a_t)) (s_0:a_t) (l:seq (step_t todo)) =
   length todo = 0
   \/ // every transaction has a corresponding `Step` operation in
      // the linearization sequence.
      forall (x:xnid_t todo).
         (exists (y:nat{y < length l}).
            let op = index l y in
            is_Step op && Step.id op = x)

val linearize:
   todo:seq (transaction_t 'a)
   -> s_0:'a
   -> e:entropy_t 'b
   -> Tot (l:seq (step_t 'a)){linearized_p todo s_0 l})
let linearize todo s_0 =
   let p = 
      map
         (fun i x ->
            Pending i s_0)
         todo
   in
   linearize_loop todo p createEmpty
*)
