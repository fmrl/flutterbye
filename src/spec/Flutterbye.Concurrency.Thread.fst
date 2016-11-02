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

type step_t 'a =
   | Commit: op:('a -> Tot 'a) -> step_t 'a
   | Stale: op:('a -> Tot 'a) -> step_t 'a

type thread_t 'a =
   {
      steps:seq (step_t 'a);
      state:'a;
   } 

type is_something_committed_p (#a_t:Type) (steps:seq (step_t a_t)) =
   satisfies_p is_Commit steps