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

   type set_g (element_t: Type) = 
      element_t -> Tot bool

   val empty: #element_t: Type -> Tot (set_g element_t)
   let empty (element_t: Type) = 
      fun _ -> false

   val is_mem: 
      #element_t: Type 
      -> set_g element_t 
      -> element_t 
      -> Tot bool
   let is_mem set = set

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
