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

type xnid_t (#a_t:Type) (xns:seq (transaction_t a_t)) =
   | XnId: as_nat:nat{as_nat < length xns} -> xnid_t xns

type pending_t (#a_t:Type) (xns:seq (transaction_t a_t)) =
   | Pending: id:xnid_t xns -> s:a_t -> pending_t xns

type step_t (#a_t:Type) (xns:seq (transaction_t a_t)) =
   | Next: id:xnid_t xns -> step_t xns
   | Studder: id:xnid_t xns -> step_t xns

type next_loop_p: 
   #a_t:Type 
   -> xns:seq (transaction_t a_t)
   -> state:a_t
   -> pending0:seq (pending_t xns)
   -> pending:seq (pending_t xns)
   -> steps:seq (step_t xns)
   -> Type
=
   fun #a_t xns state pending0 pending steps ->
      (length pending0 <= length xns)
      /\ (length pending <= length pending0)
      (*/\ (   (exists (x:nat{x < length steps}).
                is_Next (index steps x))
          \/ (exists (x:nat{x < length pending}).
                Pending.s (index pending x) = state))*)

val next_loop:
   xns:seq (transaction_t 'a)
   -> state:'a
   -> pending0:seq (pending_t xns)
   -> pending:seq (pending_t xns)
   -> steps:seq (step_t xns)
   -> Tot (steps':seq (step_t xns))
      (decreases (length pending))
let rec next_loop xns state pending0 pending steps =
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
      next_loop xns state' pending0 pending' steps'
   end

val next_loop_lemma:
   xns:seq (transaction_t 'a)
   -> state:'a
   -> pending0:seq (pending_t xns)
   -> pending:seq (pending_t xns)
   -> steps:seq (step_t xns)
   -> Lemma 
      (requires (next_loop_p xns state pending0 pending steps))
      (ensures (next_loop_p xns state pending0 createEmpty (next_loop xns state pending0 pending steps))) 
      (decreases (length pending))
let rec next_loop_lemma xns state pending0 pending steps =
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
      next_loop_lemma xns state' pending0 pending' steps'
   end

(*type next_p: 
   #a_t:Type 
   -> xns:seq (transaction_t a_t)
   -> state:a_t
   -> pending:seq (pending_t xns)
   -> steps:seq (step_t xns)
   -> Type
=
   fun #a_t xns state pending steps ->
      length pending <= length xns*)

val next:
   xns:seq (transaction_t 'a)
   -> state:'a
   -> pending:seq (pending_t xns){next_loop_p xns state pending pending createEmpty}
   -> Tot (steps:seq (step_t xns))
let next xns state pending =
   next_loop_lemma xns state pending pending createEmpty;
   next_loop xns state pending pending createEmpty

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
