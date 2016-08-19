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

type pending_t (n:nat) =
   | Pending: id:nat{id < n} -> 'a -> pending_t n

type operation_t (n:nat) =
   | Step: id:nat{id < n} -> 'a -> operation_t n
   | Studder: id:nat{id < n} -> 'a -> operation_t n

val linearize_loop:
   xs:seq (transaction_t 'a)
   -> acc_p:seq (transaction_t 'a)
   -> acc_e:entropy_t 'b
   -> acc_ops:seq (operation_t 'a)
   -> Tot (r:(seq (operation_t 'a) * (entropy_t 'b)))
let rec linearize_loop xs e ops =
   ()

val linearize:
   xs:seq (transaction_t 'a)
   -> e:entropy_t 'b
   -> Tot (r:(seq (operation_t 'a) * (entropy_t 'b)))
let linearize xs e ops =
   linearize_loop xs e createEmpty

