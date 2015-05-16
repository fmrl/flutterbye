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

   type map_g (key_t: Type) (value_t: Type) = 
      key_t -> Tot (option value_t)

   val empty: 
      #key_t: Type -> #value_t: Type -> 
      Tot (map_g key_t value_t)
   let empty (key_t: Type) (value_t: Type) = 
      fun _ -> None

   val is_mem: 
      #key_t: Type -> #value_t: Type -> 
      map_g key_t value_t -> key_t -> Tot bool
   let is_mem m k = 
      is_Some (m k)

   val lookup: 
      #key_t: Type -> #value_t: Type -> 
      map: map_g key_t value_t -> k: key_t{is_mem map k} -> Tot value_t
   let lookup map key = 
      match map key with
         | Some value ->
            value

   val domain: 
      #key_t: Type -> #value_t: Type -> 
      map_g key_t value_t -> Tot (Set.set_g key_t)
   let domain map = 
      is_mem map

   val update: 
      #key_t: Type -> #value_t: Type -> 
      map_g key_t value_t -> key_t -> value_t 
         -> Tot (map_g key_t value_t)
   let update (key_t: Type) (value_t: Type) map key value =
      (fun k ->
         if key = k then
            Some value
         else
            map k)

   val add: 
      #key_t: Type -> #value_t: Type -> 
      map: map_g key_t value_t -> key: key_t{not (is_mem map key)} -> value_t 
         -> Tot (map_g key_t value_t)
   let add (key_t: Type) (value_t: Type) map key value =
      update map key value

   val subst: 
      #key_t: Type -> #value_t: Type -> 
      map: map_g key_t value_t -> key: key_t{is_mem map key} -> value_t 
         -> Tot (map_g key_t value_t)
   let subst (key_t: Type) (value_t: Type) map key value =
      update map key value

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
