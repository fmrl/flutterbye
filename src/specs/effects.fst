(*--build-config
   other-files:ext.fst src/specs/set.fst src/specs/map.fst src/specs/seq.fst 
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

//@requires "seq.fst"

module Tesseract.Specs.Effects

   type region_id_t = nat

   type step_g (state_t: Type) (step_kind_t: Type)
      = region_id_t 
         -> state_t
         -> step_kind_t 
         -> Tot (state_t * (Seq.State (region_id_t * step_kind_t)))

   type effect_g (state_t: Type) (step_kind_t: Type) 
      =
      | Spawn: 
          state0: state_t
         -> step: step_g state_t step_kind_t
         -> effect_g state_t step_kind_t
      | Step: 
         region_id: region_id_t
         -> step_kind: step_kind_t 
         -> effect_g state_t step_kind_t

   type _log_g 
      (state_t: Type) 
      (step_kind_t: Type) 
      = Seq.State (effect_g state_t step_kind_t)

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
