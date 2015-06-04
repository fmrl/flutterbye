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

