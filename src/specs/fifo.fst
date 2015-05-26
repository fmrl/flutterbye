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

module Tesseract.Specs.Fifo

   type fifo_g (item_t: Type) 
      = { items: Seq.seq_g item_t }

   val empty: #item_t: Type -> Tot (fifo_g item_t)
   let empty (item_t: Type) 
      = { items = Seq.empty }

   val length:
      #item_t: Type
      -> fifo: fifo_g item_t
      -> Tot nat
   let length (item_t: Type) fifo
      = Seq.length fifo.items

   val peek: 
      #item_t: Type 
      -> fifo: fifo_g item_t{0 < length fifo}
      -> Tot item_t
   let peek (item_t: Type) fifo
      = Seq.first fifo.items

   val pop: 
      #item_t: Type 
      -> fifo: fifo_g item_t{0 < length fifo}
      -> Tot (fifo_g item_t)
   let pop (item_t: Type) fifo
      = { items = Seq.remove fifo.items 0 }

   val push: 
      #item_t: Type 
      -> fifo_g item_t
      -> item_t
      -> Tot (fifo_g item_t)
   let push (item_t: Type) fifo item
      = { items = Seq.insert fifo.items (length fifo) item }

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
