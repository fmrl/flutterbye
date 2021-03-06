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

module Flutterbye.Concurrency.Thread
open FStar.Seq
open Flutterbye.Seq

type ops_t (state_t:Type{hasEq state_t}) = seq (state_t -> Tot state_t)

type opcode_t (#state_t:Type{hasEq state_t}) (ops:ops_t state_t) =
   opcode:nat{opcode < length ops}

val apply_op:
   #state_t:Type{hasEq state_t}
   -> ops:ops_t state_t
   -> opcode:opcode_t ops
   -> state_t
   -> Tot (state_t)
let apply_op #state_t ops opcode state =
   let op = index ops opcode in
   op state

type transaction_t (#state_t:Type{hasEq state_t}) (ops:ops_t state_t) = {
   txnid:nat;
   opcode:opcode_t ops;
   observation:state_t
}

type step_t (#state_t:Type{hasEq state_t}) (ops:ops_t state_t) =
   | Commit: transaction:transaction_t ops -> step_t #state_t ops
   | Stale: transaction:transaction_t ops -> step_t #state_t ops

type thread_t (#state_t:Type{hasEq state_t}) (ops:ops_t state_t) = {
   pending:seq (transaction_t ops);
   steps:seq (step_t ops);
   state:state_t
}
