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

type pending_t 'a =
   | Pending: op:('a -> Tot 'a) -> observed:'a -> pending_t 'a

val is_fresh: state:'a -> pending_t 'a -> Tot bool
let is_fresh state pending =
   Pending.observed pending = state

type satisfies_fresh_p (#a_t:Type) (pending:seq (pending_t a_t)) (state:a_t) =
   satisfies_p (is_fresh state) pending

val linearize_inner_induction_loop:
      pending:seq (pending_t 'a)
   -> thread:thread_t 'a{is_something_committed_p thread.steps \/ satisfies_fresh_p pending thread.state}
   -> Tot (thread':(thread_t 'a){is_something_committed_p thread'.steps})
      (decreases (length pending))
let rec linearize_inner_induction_loop pending thread =
   if 0 = length pending then
      thread
   else begin
      let i = 0 in
      let p = index pending i in
      let op = Pending.op p in
      let fresh = (Pending.observed p = thread.state) in
      if fresh then begin
         // if the transaction is fresh, we can commit it.
         let step' = Commit op in
         let state' = op thread.state in
         let steps' = append thread.steps (create 1 step') in
         let pending' = remove pending i in
         Flutterbye.Seq.Satisfies.create_lemma 1 step';
         assert (is_something_committed_p (create 1 step'));
         Flutterbye.Seq.Satisfies.append_lemma thread.steps (create 1 step');
         assert (is_something_committed_p steps');
         let thread' = { state = state'; steps = steps' } in 
         linearize_inner_induction_loop pending' thread'
      end else begin
         // otherwise, we mark the transaction as stale.
         let step' = Stale op in
         let steps' = append thread.steps (create 1 step') in
         Flutterbye.Seq.Satisfies.append_lemma thread.steps (create 1 step');
         assert (is_something_committed_p thread.steps <==> is_something_committed_p steps');
         let pending' = remove pending i in
         Flutterbye.Seq.Satisfies.remove_lemma pending i (is_fresh thread.state);
         assert (satisfies_fresh_p pending thread.state ==> satisfies_fresh_p pending' thread.state);
         let thread' = { state = thread.state; steps = steps' } in 
         linearize_inner_induction_loop pending' thread'
      end         
   end

val linearize_inner_induction:
      pending:seq (pending_t 'a)
   -> state:'a{satisfies_fresh_p pending state}
   -> Tot (thread':(thread_t 'a){is_something_committed_p thread'.steps})
      (decreases (length pending))
let linearize_inner_induction pending state =
   let thread = { state = state; steps = createEmpty } in
   linearize_inner_induction_loop pending thread