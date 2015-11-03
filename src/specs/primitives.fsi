(*--build-config
   options:--admit_fsi Seq;
   other-files:seq.fsi
--*)

// $legal:614:
//
// Copyright 2015 Michael Lowell Roberts
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
// ,$

module Flutterbye.Specs.Primitives
   open Seq

   type EffectKind =
      | Spawn
      | Influence

   type Effect 'arg = {
         region_id:nat;
         effect_kind:EffectKind;
         arg:'arg
      }

   type Reaction 'arg 'state =
      effect:(Effect 'arg)
      -> state:'state
      -> Tot ('state * '(seq (Effect 'arg)))
                        // (consequential effects * new state)

   type Chronology = Type -> Type -> Type

   val empty:
      Reaction 'arg 'state
      -> 'state
      -> 'arg
      -> Chronology 'arg 'state

   val length: Chronology 'arg 'state -> Tot nat

   val width: Chronology 'arg 'state -> Tot nat

   val first: Chronology 'arg 'state -> Tot nat

   val event:
      c:Chronology 'arg 'state
      -> i:nat{i < length c}
      -> Tot (Effect 'arg)

   val state:
      c:Chronology 'arg 'state
      -> i:nat{i < length c}
      -> Tot 'state

   val filter:
      c:Chronology 'arg 'state
      -> r:{r < width c}
      -> Tot (Chronology 'arg 'state)

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
