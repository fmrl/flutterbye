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

module Tesseract.Specs.Set

   type set_g (item_t: Type) 
      = item_t -> Tot bool

   val empty: #item_t: Type -> Tot (set_g item_t)
   let empty (item_t: Type) 
      = fun _ -> false

   val is_mem: 
      #item_t: Type 
      -> set_g item_t 
      -> item_t 
      -> Tot bool
   let is_mem set = set

   val add: 
      #item_t: Type 
      -> set: set_g item_t 
      -> item: item_t{not (is_mem set item)} 
      -> Tot (set_g item_t)
   let add (item_t: Type) set item
      = fun i ->
            if i = item then
               true
            else
               set i
             

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
