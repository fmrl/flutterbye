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
//@requires "set.fst"

module Tesseract.Specs.History

   type event_g (context_t: Type) (message_t: Type) =
      | Spawn: 
         context: context_t 
         -> event_g context_t message_t
      | Step: 
         context: context_t 
         -> message: message_t 
         -> event_g context_t message_t

   type _history_g (context_t: Type) (message_t: Type) =
      {
         log: Seq.seq_g (event_g context_t message_t);
         spawned: Set.set_g context_t
      }

   type is_history_safe: 
      #context_t: Type 
      -> #message_t: Type 
      -> _history_g context_t message_t 
      -> Type
      = 
         fun 
            (context_t: Type) 
            (message_t: Type) 
            (_history: 
               _history_g context_t message_t) 
         ->
            // each actor id may only be spawned once.
            (forall (context: context_t).
               Set.is_mem _history.spawned context ==> 
                  1 =
                     Seq.foldl
                        (fun accum event ->
                           match event with
                              | Spawn context ->
                                 accum + 1
                              | _ ->
                                 accum)
                        0
                        _history.log)
            // all actor ids must be in the set of known ids.
            /\ (forall n.
                  0 <= n && n < Seq.length _history.log && is_Spawn (Seq.nth _history.log n)
                  ==>
                     Set.is_mem _history.spawned (Spawn.context (Seq.nth _history.log n)))

   type history_g (context_t: Type) (message_t: Type) 
      = _history: _history_g context_t message_t{is_history_safe _history}

   val init:
      #context_t: Type 
      -> #message_t: Type 
      -> Tot (history_g context_t message_t)
   let init 
      (context_t: Type) 
      (message_t: Type) 
      = 
         {
            log = Seq.empty;
            spawned = Set.empty
         }

   val is_mem:
      #context_t: Type
      -> #message_t: Type
      -> history_g context_t message_t
      -> context_t
      -> Tot bool
   let is_mem (context_t: Type) (message_t: Type) history context
      = Set.is_mem history.spawned context

   val local_events:
      #context_t: Type
      -> #message_t: Type
      -> history: history_g context_t message_t
      -> context: context_t{is_mem history context}
      -> Tot (Seq.seq_g (event_g context_t message_t))
   let local_events (context_t: Type) (message_t: Type) history context
      = 
         Seq.filter
            (fun event ->
               match event with
                  | Spawn aid ->
                     aid = context
                  | Step aid _ ->
                     aid = context)
            history.log

   val global_events:
      #context_t: Type
      -> #message_t: Type
      -> history_g context_t message_t
      -> Tot (Seq.seq_g (event_g context_t message_t))
   let global_events (context_t: Type) (message_t: Type) history
      = history.log

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$









