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
//@requires "message.fst"

module Tesseract.Specs.Actor

   type _actor_g 
      (id_t: Type) 
      (state_t: Type) 
      (event_t: Type) 
      = {
         id: id_t;
         state0: state_t;
         inbox: 
            Seq.seq_g (Message.message_g id_t event_t);
         step: 
            state_t 
            -> Message.message_g id_t event_t 
            -> Tot state_t 
      }

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$

