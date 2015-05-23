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

module Tesseract.Specs.History

   type step_g (actor_id_t: Type) (message_t: Type) =
      | Spawn: 
         actor_id: actor_id_t 
         -> step_g actor_id_t message_t
      | Message: 
         actor_id: actor_id_t 
         -> message: message_t 
         -> step_g actor_id_t message_t

   type _history_g (actor_id_t: Type) (message_t: Type) =
      {
         steps: Seq.seq_g (step_g actor_id_t message_t);
         known_ids: Set.set_g actor_id_t
      }

   type invariant: 
      #actor_id_t: Type 
      -> #message_t: Type 
      -> _history_g actor_id_t message_t 
      -> Type
      = 
         fun 
            (actor_id_t: Type) 
            (message_t: Type) 
            (_history: 
               _history_g actor_id_t message_t) 
         ->
            // each actor actor_id may only be spawned once.
            (forall (actor_id: actor_id_t).
               Set.is_mem _history.known_ids actor_id ==> 
                  1 =
                     Seq.foldl
                        (fun accum event ->
                           match event with
                              | Spawn actor_id ->
                                 accum + 1
                              | _ ->
                                 accum)
                        0
                        _history.steps)
            // all actor ids must be in the set of known ids.
            /\ (forall n.
                  0 <= n && n < Seq.length _history.steps && is_Spawn (Seq.nth _history.steps n)
                  ==>
                     Set.is_mem _history.known_ids (Spawn.actor_id (Seq.nth _history.steps n)))

   type history_g (actor_id_t: Type) (message_t: Type) 
      = _history: _history_g actor_id_t message_t{invariant _history}

   val init:
      #actor_id_t: Type 
      -> #message_t: Type 
      -> Tot (history_g actor_id_t message_t)
   let init 
      (actor_id_t: Type) 
      (message_t: Type) 
      = 
         {
            steps = Seq.empty;
            known_ids = Set.empty
         }

   val is_mem:
      #actor_id_t: Type
      -> #message_t: Type
      -> history_g actor_id_t message_t
      -> actor_id_t
      -> Tot bool
   let is_mem (actor_id_t: Type) (message_t: Type) history actor_id
      = Set.is_mem history.known_ids actor_id

   val local:
      #actor_id_t: Type
      -> #message_t: Type
      -> history: history_g actor_id_t message_t
      -> actor_id: actor_id_t{is_mem history actor_id}
      -> Tot (Seq.seq_g (step_g actor_id_t message_t))
   let local (actor_id_t: Type) (message_t: Type) history actor_id
      = 
         Seq.filter
            (fun step ->
               match step with
                  | Spawn aid ->
                     aid = actor_id
                  | Message aid _ ->
                     aid = actor_id)
            history.steps

   val global:
      #actor_id_t: Type
      -> #message_t: Type
      -> history_g actor_id_t message_t
      -> Tot (Seq.seq_g (step_g actor_id_t message_t))
   let global (actor_id_t: Type) (message_t: Type) history
      = history.steps

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$









