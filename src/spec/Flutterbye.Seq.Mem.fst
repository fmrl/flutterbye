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

module Flutterbye.Seq.Mem
open FStar.Seq
open Flutterbye.Seq.Find

type mem_p (#a_t:Type) (a:a_t) (s:seq a_t) =
   (exists (x:nat).
      x < length s && index s x = a)

val mem: x:'a -> s:seq 'a -> Tot (b:bool{b <==> mem_p x s})
let mem a s =
   is_Some (find (fun a' -> a = a') s)

abstract val index_lemma:
   s:seq 'a -> 
   Lemma
      (ensures
         // an element obtained from a sequence is a member of that sequence.  
         (length s > 0 ==> 
            (forall (x:nat).
               x < length s ==> mem_p (index s x) s)))
let index_lemma s = 
   ()

abstract val slice_lemma:
   s:seq 'a ->
   Lemma
      (ensures
         (forall (x:nat) (y:nat) (sl:seq 'a).
            // if [x, y) describe a slice of `s`, `sl`... 
            (y < length s /\ x <= y /\ equal sl (slice s x y)) ==>
               // ...then any member of the slice is a member of `s`.
               (forall (z:nat).
                  z < length sl ==> mem_p (index sl z) s)))
let slice_lemma s =
   ()

private type empty_p (#a_t:Type) (s:seq a_t) =
   forall (x:a_t).
      ~ (mem_p x s)

abstract val empty_lemma:
   s:seq 'a ->
   Lemma (ensures (length s = 0 <==> empty_p s))
let empty_lemma s = 
   if length s = 0 then
      ()
   else
      (assert (mem_p (index s 0) s); // required witness
      assert (~ (empty_p s)))

abstract val create_lemma:
   n:nat -> 
   a:'a ->
   Lemma
      (requires (True)) // required to avoid type error in SMTPat expression.
      (ensures 
         // if we are creating an empty sequence, then null membership applies.
         ((n = 0 <==> empty_p (create n a)) /\
         // otherwise, only `a` can be a member of the resulting sequence.
         (n > 0 <==> mem_p a (create n a))))
      [SMTPat (create n a)]
let create_lemma n a =
   if n = 0 then
      ()
   else
      let s = create n a in
      assert (index s 0 = a) // required witness