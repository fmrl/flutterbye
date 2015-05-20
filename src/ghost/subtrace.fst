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

module Tesseract.Ghost.Subtrace

   type step_g (state_t: Type) (event_t: Type) = 
      | Init: state: state_t -> step_g state_t event_t
      | Next: state: state_t -> event: event_t -> step_g state_t event_t

   type transform_g (state_t: Type) (event_t: Type) =
      state_t -> event_t -> Tot state_t

   type subtrace_g (state_t: Type) (event_t: Type) =
      {
         event_log: Seq.seq_g event_t;
         transform: transform_g state_t event_t;
         state0: state_t
      }

   val init: 
      #state_t: Type -> #event_t: Type -> 
      transform_g state_t event_t -> state_t -> Tot (subtrace_g state_t event_t)
   let init (state_t: Type) (event_t: Type) f s = 
      {
         event_log = Seq.empty;
         transform = f;
         state0 = s
      }

   val steps:
      #state_t: Type -> #event_t: Type -> 
      subtrace_g state_t event_t -> Tot (Seq.seq_g (step_g state_t event_t))
   let steps (state_t: Type) (event_t: Type) subtrace =
      let head = Seq.single (Init subtrace.state0) in
      let tail =
         Seq.foldl
            (fun (accum: Seq.seq_g (step_g state_t event_t){0 < Seq.length accum}) event ->
               let step = 
                  (let state = 
                     match Seq.last accum with
                        | Init s ->
                           s
                        | Next s _ ->
                           s
                  in
                     Next (subtrace.transform state event) event)
               in
                  Seq.append accum step)
            head
            subtrace.event_log
      in
         Seq.concat head tail

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
