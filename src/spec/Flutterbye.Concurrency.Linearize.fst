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

module Flutterbye.Concurrency.Linearize
open FStar.Seq
open Flutterbye.Seq
open Flutterbye.Concurrency.Thread

val is_transaction_fresh:
      #state_t:Type
   -> ops:ops_t state_t
   -> state_t
   -> transaction_t ops
   -> Tot bool
let is_transaction_fresh #state_t ops state txn =
   txn.observation = state

type one_transaction_is_fresh_p
   (#state_t:Type)
   (ops:ops_t state_t)
   (state:state_t)
   (txns:seq (transaction_t ops))
=
   contains_p (is_transaction_fresh ops state) txns

val linearize_step_loop:
      state_t:Type
   -> ops:ops_t state_t
   -> accum:thread_t ops{
            contains_p (is_Commit) accum.steps
         \/ one_transaction_is_fresh_p ops accum.state accum.pending
      }
   -> Tot (accum':thread_t ops{contains_p (is_Commit) accum'.steps})
      (decreases (length accum.pending))
let rec linearize_step_loop state_t ops accum =
   if 0 = length accum.pending then
      accum
   else begin
      let i = 0 in
      let picked = index accum.pending i in
      if is_transaction_fresh ops accum.state picked then begin
         // if the picked transaction is fresh, we can commit it.
         let step' = Commit picked in
         let accum' = {
            state = apply_op ops picked.opcode accum.state;
            pending = remove accum.pending i;
            steps = append accum.steps (create 1 step')
         }
         in
         Flutterbye.Seq.Contains.create_lemma 1 step';
         assert (contains_p (is_Commit) (create 1 step'));
         Flutterbye.Seq.Contains.append_lemma 
            accum.steps (create 1 step') (is_Commit);
         assert (contains_p (is_Commit) accum'.steps);
         linearize_step_loop state_t ops accum'
      end
      else begin
         // otherwise, we mark the transaction as stale.
         let step' = Stale picked in
         let accum' = {
            state = accum.state;
            pending = remove accum.pending i;
            steps = append accum.steps (create 1 step')
         }
         in
         Flutterbye.Seq.Contains.append_lemma 
            accum.steps (create 1 step') (is_Commit);
         assert (contains_p (is_Commit) accum.steps <==> contains_p (is_Commit) accum'.steps);
         Flutterbye.Seq.Contains.remove_lemma accum.pending i (is_transaction_fresh ops accum.state);
         assert (
                one_transaction_is_fresh_p ops accum.state accum.pending
            ==> one_transaction_is_fresh_p ops accum.state accum'.pending
         );
         linearize_step_loop state_t ops accum'
      end
   end

type all_transactions_are_fresh_p
   (#state_t:Type)
   (ops:ops_t state_t)
   (state:state_t)
   (txns:seq (transaction_t ops))
=
   forall (i:nat{i < length txns}).
      is_transaction_fresh ops state (index txns i)

val refresh_loop:
      #state_t:Type
   -> ops:ops_t state_t
   -> state:state_t
   -> steps:seq (step_t ops)
   -> i:nat{i <= length steps}
   -> accum:seq (transaction_t ops){
         all_transactions_are_fresh_p ops state accum
      }
   -> Tot (accum':seq (transaction_t ops){
         all_transactions_are_fresh_p ops state accum'
      })
      (decreases (length steps - i))
let rec refresh_loop #state_t ops state steps i accum =
   if i = length steps then begin
      accum
   end
   else begin
      let step = index steps i in
      if is_Stale step then
         let fresh_txn = {
            txnid = (Stale.transaction step).txnid;
            opcode = (Stale.transaction step).opcode;
            observation = state
         }
         in
         let accum' = append accum (create 1 fresh_txn) in
         refresh_loop ops state steps (i + 1) accum'
      else
         refresh_loop ops state steps (i + 1) accum
   end

val linearize_step:
      #state_t:Type
   -> ops:ops_t state_t
   -> thread:thread_t ops{
         one_transaction_is_fresh_p ops thread.state thread.pending
      }
   -> Tot (thread':thread_t ops{
            length thread'.pending = 0
         \/ all_transactions_are_fresh_p ops thread'.state thread'.pending
      })
let linearize_step #state_t ops thread =
   let thread_1 = linearize_step_loop state_t ops thread in
   let pending' =
      refresh_loop ops thread_1.state thread_1.steps 0 createEmpty
   in
   let thread_2 = {
         state = thread_1.state;
         pending = pending';
         steps = append thread.steps thread_1.steps
   }
   in
   thread_2
