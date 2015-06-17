// $legal:614:
// 
// Copyright 2015 Michael Lowell Roberts
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 
// ,$

//@requires "set.fst"

module Tesseract.Specs.Map

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
