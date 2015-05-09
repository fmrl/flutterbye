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

module Tesseract.Ghost.Set

   type set 'lmnt = 
      { 
         mem: 'lmnt -> Tot bool
      }

   val empty: #lmnt_t: Type -> set lmnt_t
   let empty (lmnt_t: Type) = 
      {
         mem = (fun (e: lmnt_t) -> false)
      }

   let mem m = m.mem

   val arbitrary: #lmnt_t: Type -> #val_t: Type -> (lmnt_t -> Tot bool) -> Tot (set lmnt_t)
   let arbitrary fn =
      {
         mem = fn
      }

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
