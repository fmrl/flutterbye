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

type pending_t 'a =
   | Pending: op:('a -> Tot 'a) -> observed:'a -> pending_t 'a

type step_t 'a =
   | Commit: op:('a -> Tot 'a) -> step_t 'a
   | Stale: op:('a -> Tot 'a) -> step_t 'a

type contains_commit_p (#a_t:Type) (steps:seq (step_t a_t)) =
   length steps > 0
   /\ (exists (x:nat{x < length steps}).
         is_Commit (index steps x))

type contains_fresh_p (#a_t:Type) (pending:seq (pending_t a_t)) (state:a_t) =
   length pending > 0
   /\ (exists (x:nat{x < length pending}).
         Pending.observed (index pending x) = state)

(*type advance_loop_invariants_p 
   (#a_t:Type) 
   (pending0:seq (pending_t a_t)) 
   (pending:seq (pending_t a_t))
   (state:'a)
   (steps:seq (step_t a_t))
=     (length pending <= length pending0)
   /\ (contains_commit_p steps \/ contains_fresh_p pending state)*)

val advance_loop:
      pending:seq (pending_t 'a)
   -> state:'a
   -> steps:seq (step_t 'a){contains_commit_p steps \/ contains_fresh_p pending state}
   -> Tot (steps':seq (step_t 'a){contains_commit_p steps'})
      (decreases (length pending))
let rec advance_loop pending state steps =
   if 0 = length pending then
      steps
   else begin
      let i = 0 in
      let p = index pending i in
      let op = Pending.op p in
      let fresh = (Pending.observed p = state) in
      if fresh then begin
         admit ();
         let step' = Commit op in
         let state' = op state in
         let steps' = append steps (create 1 step') in
         let pending' = remove pending i in
         advance_loop pending' state' steps'
      end else begin
         admit ();
         let step' = Stale op in
         let steps' = append steps (create 1 step') in
         let pending' = remove pending i in
         advance_loop pending' state steps'
      end         
   end

(*val advance_loop_lemma:
      pending0:seq (pending_t 'a)
   -> pending:seq (pending_t 'a)
   -> state:'a
   -> steps:seq (step_t 'a)
   -> Lemma 
      (requires (True))
      (ensures (True)) 
      (decreases (length pending))
let rec advance_loop_lemma pending0 pending state steps =
   if 0 = length pending then
      ()
   else begin
      let i = 0 in
      let p = index pending i in
      let fresh = (Pending.observed p = state) in
      let op = Pending.op p in
      let step' =
         if fresh then
            Commit op
         else
            Stale op
      in
      let state' =
         if fresh then
            op state
         else
            state
      in
      let steps' = append steps (create 1 step') in
      let pending' = remove pending i in
      advance_loop_lemma pending0 pending' state' steps'
   end*)

(*type advanced_p (pending:seq (pending_t 'a)) (state:'a) (steps:seq (step_t 'a)) =
   length pending <= length xns

val advance:
   xns:seq (transaction_t 'a)
   -> state:'a
   // todo: eliminiate need for `has_fresh_p`.
   -> pending:seq (pending_t xns){length pending <= length xns /\ has_fresh_pending_p xns pending state}
   -> Tot (steps:seq (step_t xns){advance_p xns pending state steps})
let advance xns state pending =
   advance_loop_lemma xns pending state pending createEmpty;
   advance_loop xns pending state pending createEmpty*)

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
