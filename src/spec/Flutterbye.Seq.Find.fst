// $legal:629:
//
// Copyright 2016 Michael Lowell Roberts & Microsoft Research
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
//,$

module Flutterbye.Seq.Find
open FStar.Seq
open Flutterbye.Option

private type found_p (#a_t:Type) (f:(a_t -> Tot bool)) (s:seq a_t) (i:option nat) =
   // if not found...
   (is_None i <==>
      // ...then no element is `s` can satisfy predicate `f`.
      (forall (x:nat).
         x < length s ==> not (f (index s x)))) /\
   // otherwise, if found...
   (is_Some i ==> 
      // ...then `i` must index an element of `s`.
      (b2t (get i < length s) /\
      // ...and `i` must point to an element that satisfies predicate `f`.
      b2t (f (index s (get i))) /\
      // ...and every element preceeding the element indexed by `i` must not satisfy predicate `f`.
      (get i > 0 ==>
         (forall (x:nat).
            x < get i ==> not (f (index s x))))))

private val find_loop:
      f:('a -> Tot bool)
   -> s:seq 'a
   -> i:nat{i <= length s}
   -> ac:(option nat){found_p f (slice s 0 i) ac}
   -> Tot (ac':option nat{found_p f s ac'})
      (decreases (length s - i))
let rec find_loop f s i ac =
   if i < length s then
      let ac' =
         if is_None ac && (f (index s i)) then
            Some i
         else
            ac in
      find_loop f s (i + 1) ac'
   else
      ac

val find: 
   f:('a -> Tot bool) -> 
   s:seq 'a -> 
   Tot (i:option nat{found_p f s i})
let find f s =
   find_loop f s 0 None
