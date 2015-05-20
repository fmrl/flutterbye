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

module Tesseract.Specs.Actor
   
   type _step_g (state_t: Type) (event_t: Type) = 
      | Spawn: state: state_t -> step_g state_t event_t
      | Service: state: state_t -> event: event_t -> step_g state_t event_t

   type transform_g (state_t: Type) (event_t: Type) =
      state_t -> (state_t -> event_t) -> Tot state_t

   type actor_g (state_t: Type) (event_t: Type) =
      {
         event_log: Seq.seq_g (state_t -> event_t);
         transform: transform_g state_t event_t;
         state0: state_t
      }

   val spawn: 
      #state_t: Type 
      -> #event_t: Type
      -> transform_g state_t event_t 
      -> state_t 
      -> Tot (actor_g state_t event_t)
   let spawn (state_t: Type) (event_t: Type) f s = 
      {
         event_log = Seq.empty;
         transform = f;
         state0 = s
      }

   val steps:
      #state_t: Type 
      -> #event_t: Type 
      -> actor_g state_t event_t 
      -> Tot (Seq.seq_g (step_g state_t (state_t -> event_t)))
   let steps (state_t: Type) (event_t: Type) actor =
      let head = Seq.single (Spawn actor.state0) in
      let tail =
         Seq.foldl
            (fun (accum: Seq.seq_g (step_g state_t event_t){0 < Seq.length accum}) event ->
               let step = 
                  (let state = 
                     match Seq.last accum with
                        | Spawn s ->
                           s
                        | Service s _ ->
                           s
                  in
                     Service (actor.transform state event) event)
               in
                  Seq.append accum step)
            head
            actor.event_log
      in
         Seq.concat head tail

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
