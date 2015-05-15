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

   type map =
      fun (key_t: Type) (val_t: Type) ->
         key_t -> Tot (option val_t)

   val empty: #key_t: Type -> #val_t: Type -> Tot (map key_t val_t)
   let empty (key_t: Type) (val_t: Type) = 
      fun _ -> 
         None

   val mem: #key_t: Type -> #val_t: Type -> map key_t val_t -> key_t -> Tot bool
   let mem m k = is_Some (m k)

   val lookup: #key_t: Type -> #val_t: Type -> m: map key_t val_t -> k: key_t{mem m k} -> Tot val_t
   let lookup m k = 
      match m k with
         | Some v ->
            v

   val domain: #key_t: Type -> #val_t: Type -> map key_t val_t -> Tot (Set.set key_t)
   let domain m = 
      Set.arbitrary (mem m)

   val update: #key_t: Type -> #val_t: Type -> map key_t val_t -> key_t -> val_t -> Tot (map key_t val_t)
   let update (key_t: Type) (val_t: Type) m k v =
      (fun kk ->
         if k = kk then
            Some v
         else
            m kk)

   val add: #key_t: Type -> #val_t: Type -> m: map key_t val_t -> k: key_t{not (mem m k)} -> val_t -> Tot (map key_t val_t)
   let add (key_t: Type) (val_t: Type) m k v =
      update m k v

   val subst: #key_t: Type -> #val_t: Type -> m: map key_t val_t -> k: key_t{mem m k} -> val_t -> Tot (map key_t val_t)
   let subst (key_t: Type) (val_t: Type) m k v =
      update m k v

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
