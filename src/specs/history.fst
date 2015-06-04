// $legal:322:
// 
// This work is licensed under the Creative Commons
// Attribution-NonCommercial-ShareAlike 4.0 International
// License. To view a copy of this license, visit
// http://creativecommons.org/licenses/by-nc-sa/4.0/
// or send a letter to:
// 
// Creative Commons
// PO Box 1866
// Mountain View, CA 94042
// USA
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









