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

//@requires "set.fst"

module Tesseract.Ghost.Map

   type map 'key 'value = 
      { 
         maybe_lookup: 'key -> Tot (option 'value)
      }

   val empty: #key_t: Type -> #val_t: Type -> map key_t val_t
   let empty (key_t: Type) (val_t: Type) = 
      {
         maybe_lookup = (fun (k: key_t) -> (None <: option val_t))
      }

   let maybe_lookup m = m.maybe_lookup

   val mem: #key_t: Type -> #val_t: Type -> map key_t val_t -> key_t -> Tot bool
   let mem m k = is_Some (maybe_lookup m k)

   val lookup: #key_t: Type -> #val_t: Type -> m: map key_t val_t -> k: key_t{mem m k} -> Tot val_t
   let lookup m k = 
      match maybe_lookup m k with
         | Some v ->
            v

   val domain: #key_t: Type -> #val_t: Type -> map key_t val_t -> Tot (Set.set key_t)
   let domain m = 
      Set.arbitrary (mem m)

   val arbitrary: #key_t: Type -> #val_t: Type -> (key_t -> Tot (option val_t)) -> Tot (map key_t val_t)
   let arbitrary fn =
      {
         maybe_lookup = fn
      }

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
