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
      #state_t:Type{hasEq state_t}
   -> ops:ops_t state_t
   -> state_t
   -> transaction_t ops
   -> Tot bool
let is_transaction_fresh #state_t ops state txn =
   txn.observation = state

type one_transaction_is_fresh_p
   (#state_t:Type{hasEq state_t})
   (ops:ops_t state_t)
   (state:state_t)
   (txns:seq (transaction_t ops))
=
   contains_p (is_transaction_fresh ops state) txns

type step_length_invariant_p
   (#state_t:Type{hasEq state_t})
   (ops:ops_t state_t)
   (txn_count:nat)
   (accum:thread_t ops)
=
  b2t (
        txn_count
        = length accum.steps + length accum.pending
  )

type step_forthcoming_p
   (#state_t:Type{hasEq state_t})
   (ops:ops_t state_t)
   (txn_count:nat)
   (accum:thread_t ops)
=
   step_length_invariant_p ops txn_count accum
   /\ (
         one_transaction_is_fresh_p ops accum.state accum.pending
         \/ contains_p (Commit?) accum.steps
   )

type step_taken_p
   (#state_t:Type{hasEq state_t})
   (ops:ops_t state_t)
   (txn_count:nat)
   (accum:thread_t ops)
=
  step_length_invariant_p ops txn_count accum
  /\ contains_p (Commit?) accum.steps

val linearize_step_loop:
      state_t:Type{hasEq state_t}
   -> ops:ops_t state_t
   -> txn_count:nat
   -> accum:thread_t ops{step_forthcoming_p ops txn_count accum}
   -> Tot (accum':thread_t ops{step_taken_p ops txn_count accum'})
      (decreases (length accum.pending))
let rec linearize_step_loop state_t ops txn_count accum =
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
         Flutterbye.Seq.Contains.create_lemma 1 step' (Commit?);
         assert (contains_p (Commit?) (create 1 step'));
         Flutterbye.Seq.Contains.append_lemma
            accum.steps (create 1 step') (Commit?);
         assert (contains_p (Commit?) accum'.steps);
         linearize_step_loop state_t ops txn_count accum'
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
            accum.steps (create 1 step') (Commit?);
         assert (contains_p (Commit?) accum.steps <==> contains_p (Commit?) accum'.steps);
         Flutterbye.Seq.Contains.remove_lemma accum.pending i (is_transaction_fresh ops accum.state);
         assert (
                one_transaction_is_fresh_p ops accum.state accum.pending
            ==> one_transaction_is_fresh_p ops accum.state accum'.pending
         );
         linearize_step_loop state_t ops txn_count accum'
      end
   end

type all_transactions_are_fresh_p
   (#state_t:Type{hasEq state_t})
   (ops:ops_t state_t)
   (state:state_t)
   (txns:seq (transaction_t ops))
=
   forall (i:nat{i < length txns}).
      is_transaction_fresh ops state (index txns i)

type refresh_loop_invariant_p
   (#state_t:Type{hasEq state_t})
   (ops:ops_t state_t)
   (state:state_t)
   (steps:seq (step_t ops))
   (accum:seq (transaction_t ops))
=
   all_transactions_are_fresh_p ops state accum
   /\ b2t (length accum = count (Stale?) steps)

val refresh_loop:
      #state_t:Type{hasEq state_t}
   -> ops:ops_t state_t
   -> state:state_t
   -> steps:seq (step_t ops)
   -> i:nat{i <= length steps}
   -> accum:seq (transaction_t ops){
         refresh_loop_invariant_p ops state (slice steps 0 i) accum
      }
   -> Tot (accum':seq (transaction_t ops){
         refresh_loop_invariant_p ops state steps accum'
      })
      (decreases (length steps - i))
let rec refresh_loop #state_t ops state steps i accum =
   let s_1 = slice steps 0 i in
   if i = length steps then begin
      assert (equal s_1 steps);
      accum
   end
   else begin
      let s_2 = slice steps 0 (i + 1) in
      let step = index steps i in
      let s_3 = append s_1 (create 1 step) in
      assert (equal s_3 s_2);
      Flutterbye.Seq.Count.append_lemma s_1 (create 1 step) (Stale?);
      if Stale? step then
         let fresh_txn = {
            txnid = (Stale?.transaction step).txnid;
            opcode = (Stale?.transaction step).opcode;
            observation = state
         }
         in
         let accum' = append accum (create 1 fresh_txn) in
         assert (count (Stale?) s_1 + 1 = count (Stale?) s_2);
         assert (refresh_loop_invariant_p ops state s_2 accum');
         refresh_loop ops state steps (i + 1) accum'
      else begin
         assert (count (Stale?) s_1 = count (Stale?) s_2);
         assert (refresh_loop_invariant_p ops state s_2 accum);
         refresh_loop ops state steps (i + 1) accum
      end
   end

// todo: not yet saying anything about commit counts.
val linearize_step:
      #state_t:Type{hasEq state_t}
   -> ops:ops_t state_t
   -> thread:thread_t ops{
         one_transaction_is_fresh_p ops thread.state thread.pending
      }
   -> Tot (thread':thread_t ops{
            length thread'.pending < length thread.pending
         /\ all_transactions_are_fresh_p ops thread'.state thread'.pending
      })
let linearize_step #state_t ops thread =
   let accum_1 = {
         pending = thread.pending;
         steps = createEmpty;
         state = thread.state
   }
   in
   let accum_2 =
      linearize_step_loop state_t ops (length thread.pending) accum_1
   in
   let pending' =
      refresh_loop ops accum_2.state accum_2.steps 0 createEmpty
   in
   let accum_3 = {
         state = accum_2.state;
         pending = pending';
         steps = append thread.steps accum_2.steps
   }
   in
   accum_3

