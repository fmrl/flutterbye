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

type pending_t (#a_t:Type) (s_xn:seq (transaction_t a_t)) =
   | Pending: id:nat{id < length s_xn} -> s:a_t -> pending_t s_xn

type operation_t (#a_t:Type) (s_xn:seq (transaction_t a_t)) =
   | Step: id:nat{id < length s_xn} -> s:a_t -> operation_t s_xn
   | Studder: id:nat{id < length s_xn} -> operation_t s_xn

(*val linearize_loop:
   s_xn:seq (transaction_t 'a)
   -> s_0:'a
   -> e:entropy_t 'b
   -> p:seq (pending_t 'a)
   -> l:seq (operation_t 'a)
   -> Tot (l':(seq (operation_t 'a) * (entropy_t 'b)))
let rec linearize_loop s_xn e p l =
   ()*)

type linearized_p (#a_t:Type) (#b_t:Type) (s_xn:seq (transaction_t a_t)) (s_0:a_t) (e:entropy_t b_t) (t_le:(seq (operation_t s_xn) * (entropy_t b_t))) =
   length s_xn = 0
   \/ (forall (x:nat{x < length s_xn}).
         (exists (y:nat{y < length (fst t_le)}).
            let op = index (fst t_le) y in
            is_Step op && Step.id op = x))

(*val linearize:
   s_xn:seq (transaction_t 'a)
   -> s_0:'a
   -> e:entropy_t 'b
   -> Tot (l:(seq (operation_t 'a) * (entropy_t 'b)))
let linearize s_xn s_0 e =
   let p = 
      map
         (fun i x ->
            Pending i s_0)
         s_xn
   in
   linearize_loop s_xn e p createEmpty
*)

