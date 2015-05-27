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

