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
