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

module Flutterbye.Order

type compare_t 'a = 'a -> 'a -> Tot bool

private type reflexive_p (#a_t:Type) (lte:compare_t a_t) =
   forall x. lte x x

private type antisymmetric_p (#a_t:Type) (lte:compare_t a_t) =
   forall x y. ((lte x y && lte y x) <==> (x = y))

private type transitive_p (#a_t:Type) (lte:compare_t a_t) =
   forall x y z. ((lte x y && lte y z) ==> lte x z)

private type total_p (#a_t:Type) (lte:compare_t a_t) =
   forall x y. (lte x y || lte y x)

type partial_order_p (#a_t:Type) (lte:compare_t a_t) =
   reflexive_p lte /\ antisymmetric_p lte /\ transitive_p lte

type total_order_p (#a_t:Type) (lte:compare_t a_t) =
   partial_order_p lte /\ total_p lte




