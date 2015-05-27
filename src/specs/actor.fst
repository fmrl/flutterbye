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

//@requires "fifo.fst"
//@requires "history.fst"
//@requires "message.fst"

module Tesseract.Specs.Actor

   type _actor_g (actor_id_t: Type) (state_t: Type) (event_t: Type) =
      {
         id: actor_id_t;
         state0: state_t;
         inbox: Fifo.fifo_g (Message.message_g actor_id_t event_t);
         history: 
            History.history_g 
               actor_id_t 
               (Message.message_g actor_id_t event_t)
      }

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$

