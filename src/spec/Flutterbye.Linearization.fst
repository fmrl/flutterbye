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

type satisfies_commit_p (#a_t:Type) (steps:seq (step_t a_t)) =
   satisfies_p is_Commit steps

type satisfies_fresh_p (#a_t:Type) (pending:seq (pending_t a_t)) (state:a_t) =
   satisfies_p (fun p -> Pending.observed p = state) pending

val advance_loop:
      pending:seq (pending_t 'a)
   -> state:'a
   -> steps:seq (step_t 'a){satisfies_commit_p steps \/ satisfies_fresh_p pending state}
   -> Tot (steps':seq (step_t 'a){satisfies_commit_p steps'})
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
         let step' = Commit op in
         let state' = op state in
         let steps' = append steps (create 1 step') in
         let pending' = remove pending i in
         Flutterbye.Seq.Satisfies.create_lemma 1 step';
         assert (satisfies_commit_p (create 1 step'));
         Flutterbye.Seq.Satisfies.append_lemma steps (create 1 step');
         assert (satisfies_commit_p steps');
         advance_loop pending' state' steps'
      end else begin
         let step' = Stale op in
         let steps' = append steps (create 1 step') in
         let pending' = remove pending i in
         Flutterbye.Seq.Satisfies.append_lemma steps (create 1 step');
         assert (satisfies_commit_p steps <==> satisfies_commit_p steps');
         admitP (satisfies_fresh_p pending state <==> satisfies_fresh_p pending' state);
         advance_loop pending' state steps'
      end         
   end

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
