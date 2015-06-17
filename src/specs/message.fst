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

module Tesseract.Specs.Message

   type message_g (actor_id_t: Type) (event_t: Type) 
      =
         {
            sender: actor_id_t;
            recipient: actor_id_t;
            ordinal: nat;
            event: event_t
         }

   type log_g (actor_id_t: Type) (event_t: Type) 
      = Seq.seq_g (message_g actor_id_t event_t)

   val append_new: 
      #actor_id_t: Type 
      -> #event_t: Type 
      -> log_g actor_id_t event_t
      -> actor_id_t 
      -> actor_id_t 
      -> event_t 
      -> Tot (log_g actor_id_t event_t)
   let append_new 
      (actor_id_t: Type) 
      (event_t: Type) 
      log 
      sender
      recipient
      event
      =
         let message =
            {
               sender = sender;
               recipient = recipient;
               ordinal = Seq.length log;
               event = event
            }
         in
            Seq.append log message

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$

