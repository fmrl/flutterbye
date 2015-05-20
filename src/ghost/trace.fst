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

//@requires "subtrace.fst"

module Tesseract.Ghost.Trace

   type state_g (key_t: Type) (substate_t: Type) (subevent_t: Type) =
      {
         ordinal: nat;
         children: 
            Map.map_g 
               key_t 
               (substate_t * (Subtrace.transform_g substate_t subevent_t))
      }

   type _event_g (key_t: Type) (substate_t: Type) (subevent_t: Type) =
      | Spawn: 
         key: key_t 
         -> step: Subtrace.transform_g substate_t subevent_t 
         -> substate0: substate_t 
         -> _event_g key_t substate_t subevent_t
      | Service: 
         key: key_t 
         -> subevent: subevent_t 
         -> _event_g key_t substate_t subevent_t

   type is_event_safe: 
      #key_t: Type 
      -> #substate_t: Type 
      -> #subevent_t: Type
      -> state: state_g key_t substate_t subevent_t 
      -> event: _event_g key_t substate_t subevent_t
      -> Type 
      = fun 
            (key_t: Type) 
            (substate_t: Type) 
            (subevent_t: Type) 
            state 
            event 
         ->
            // spawn events may only be issued when the actor isn't yet in the set of spawned actors.
            (is_Spawn event ==> not (Map.is_mem state.children (Spawn.key event)))
            /\ // service events may only be issued when the actor is already in the set of spawned actors.
               (is_Service event ==> Map.is_mem state.children (Service.key event))

   type event_g:
      key_t: Type 
      -> substate_t: Type 
      -> subevent_t: Type 
      -> state_g key_t substate_t subevent_t 
      -> Type 
      = fun 
            (key_t: Type)
            (substate_t: Type)
            (subevent_t: Type)
            (state: 
               state_g key_t substate_t subevent_t)
         -> 
            event: 
               _event_g key_t substate_t subevent_t{is_event_safe state event}

   type trace_g (key_t: Type) (substate_t: Type) (subevent_t: Type) = 
      Subtrace.subtrace_g
         (state_g key_t substate_t subevent_t)
         (_event_g key_t substate_t subevent_t) 

   val transform: 
      #key_t: Type 
      -> #substate_t: Type 
      -> #subevent_t: Type 
      -> state: state_g key_t substate_t subevent_t
      -> event: 
            _event_g key_t substate_t subevent_t{is_event_safe state event}
      //-> event: event_g key_t substate_t subevent_t state
      -> Tot (state_g key_t substate_t subevent_t)
   let transform 
      (key_t: Type) 
      (substate_t: Type) 
      (subevent_t: Type) 
      state 
      event 
      = let ordinal' = state.ordinal + 1 in
         match event with
            | Spawn key xform substate0 ->
               {
                  ordinal = ordinal';
                  children = 
                     Map.add state.children key (substate0, xform)
               }
            | Service key subevent ->
               (match Map.lookup state.children key with
                  | (substate, xform) ->
                     let substate' = xform substate subevent in
                        {
                           ordinal = ordinal';
                           children = 
                              Map.subst state.children key (substate', xform)
                        })

   val init:
      #key_t: Type 
      -> #substate_t: Type 
      -> #subevent_t: Type 
      -> Tot (trace_g key_t substate_t subevent_t)
   let init 
      (key_t: Type) 
      (substate_t: Type) 
      (subevent_t: Type) 
      = 
         Subtrace.init 
            (transform) 
            ({
               ordinal = 0;
               children = Map.empty
            })

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$









