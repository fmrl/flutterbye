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

val is_fresh:
      #state_t:Type{hasEq state_t}
   -> ops:ops_t state_t
   -> state_t
   -> transaction_t ops
   -> Tot bool
let is_fresh #state_t ops state txn =
   txn.observation = state

val linearize_step_loop:
      state_t:Type{hasEq state_t}
   -> ops:ops_t state_t
   -> accum:thread_t ops{
            satisfies_p Commit? accum.steps
         \/ satisfies_p (is_fresh ops accum.state) accum.pending
      }
   -> Tot (accum':thread_t ops{satisfies_p Commit? accum'.steps})
      (decreases (length accum.pending))
let rec linearize_step_loop state_t ops accum =
   if 0 = length accum.pending then
      accum
   else begin
      let i = 0 in
      let picked = index accum.pending i in
      if picked.observation = accum.state then begin
         // if the picked transaction is fresh, we can commit it.
         let step' = Commit picked in
         let state' = apply_op ops picked.opcode accum.state in
         let steps' = append accum.steps (create 1 step') in
         let pending' = remove accum.pending i in
         let accum' = {
            state = state';
            pending = pending';
            steps = steps'
         }
         in
         Flutterbye.Seq.Satisfies.create_lemma 1 step';
         assert (satisfies_p Commit? (create 1 step'));
         Flutterbye.Seq.Satisfies.append_lemma accum.steps (create 1 step');
         assert (satisfies_p Commit? steps');
         linearize_step_loop state_t ops accum'
      end
      else begin
         // otherwise, we mark the transaction as stale.
         let step' = Stale picked in
         let steps' = append accum.steps (create 1 step') in
         let pending' = remove accum.pending i in
         let accum' = {
            state = accum.state;
            pending = pending';
            steps = steps'
         } in
         Flutterbye.Seq.Satisfies.append_lemma accum.steps (create 1 step');
         assert (satisfies_p Commit? accum.steps <==> satisfies_p Commit?  steps');
         Flutterbye.Seq.Satisfies.remove_lemma accum.pending i (is_fresh ops accum.state);
         assert (satisfies_p (is_fresh ops accum.state) accum.pending ==> satisfies_p (is_fresh ops accum.state) pending');
         linearize_step_loop state_t ops accum'
      end
   end

val linearize_step:
      state_t:Type{hasEq state_t}
   -> ops:ops_t state_t
   -> pending:seq (transaction_t ops)
   -> state:state_t{satisfies_p (is_fresh ops state) pending}
   -> Tot (thread':(thread_t ops){satisfies_p Commit? thread'.steps})
let linearize_step state_t ops pending state =
   let thread = { state = state; pending = pending; steps = createEmpty } in
   linearize_step_loop state_t ops thread
