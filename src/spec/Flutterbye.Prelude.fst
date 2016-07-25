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

module Flutterbye.Prelude

type address_t = | Address: id:nat -> address_t
type op_t 'a = | Op: id:nat -> opnd:'a -> op_t 'a
type effect_t 'a = | Effect: dest:address_t -> op:op_t 'a -> effect_t 'a

type next_t 'a 'b = 
   | Next: next:'a -> fx:seq (effect_t 'b) -> next_t 'a 'b

type step_t 'a 'b = 
   a:'a -> b:'b -> Tot (next_t 'a 'b)

