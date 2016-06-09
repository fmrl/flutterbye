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

module Flutterbye.Seq.Unique
open FStar.Seq
open FStar.Set
open FStar.Ghost

type unique_t (#a:Type) (s:seq a) =
   0 = length s
   \/ (forall (i:nat) (j:nat).
         i < length s
         && j < length s
         && index s j = index s i
         ==>
            j == i)

private val to_set__loop:
   // input sequence
   s:seq 'a{unique_t s}
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, the output set.
   -> c:set 'a
   -> Tot (set 'a)
      (decreases (length s - i))
let rec to_set__loop s i c =
   if i < length s then
      let a = index s i in
      let c' = union c (singleton a) in
      to_set__loop s (i + 1) c'
   else
      c

val to_set: (s:seq 'a{unique_t s}) -> Tot (set 'a)
let to_set s =
   to_set__loop s 0 empty

private val unique__loop:
   // input sequence
   s:seq 'a
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, the output sequence.
   -> c:seq 'a{unique_t c}
   -> Tot (c':seq 'a{unique_t c'})
      (decreases (length s - i))
let rec unique__loop s i c =
   if i < length s then
      let a = index s i in
      let c' =
         if Flutterbye.Seq.Mem.mem a c then
            c
         else
            append c (create 1 a) in
      unique__loop s (i + 1) c'
   else
      c

val unique: (s:seq 'a) -> Tot (u:seq 'a{unique_t u})
let unique s =
   unique__loop s 0 createEmpty

abstract val lemma__empty:
   s:seq 'a
   -> Lemma
      (requires (length s = 0))
      (ensures (unique_t s))
let lemma__empty s = ()

// mem_eq_t: membership equality
private type mem_eq_t (#a:Type) (s_0:seq a{unique_t s_0}) (s_1:set a) =
   forall x.
      Flutterbye.Seq.Mem.mem_t x s_0 <==> b2t (mem x s_1)

private val lemma__to_set__loop:
   // input sequence
   s:seq 'a{unique_t s}
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, the output set.
   -> c:set 'a
   -> Lemma
      (requires
         (((i = 0) ==> FStar.Set.equal c empty)
         /\ (mem_eq_t (slice s 0 i) c)))
      (ensures (mem_eq_t s (to_set__loop s i c)))
      (decreases (length s - i))
let rec lemma__to_set__loop s i c =
   if i < length s then
      let a = index s i in
      let c' = union c (singleton a) in
      Flutterbye.Seq.Mem.lemma__slice_2 a s;
      assert (Flutterbye.Seq.Mem.mem_t a (slice s 0 (i + 1)));
      lemma__to_set__loop s (i + 1) c'
   else
      ()

abstract val lemma__to_set:
   x:'a
   -> s:seq 'a{unique_t s}
   -> Lemma
      (requires (True))
      (ensures (Flutterbye.Seq.Mem.mem_t x s <==> mem x (to_set s)))
let lemma__to_set x s =
   lemma__to_set__loop s 0 empty

private val lemma__unique__length__loop:
   // input sequence
   s:seq 'a
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, the output set.
   -> c:seq 'a{unique_t c}
   -> Lemma
      (requires (length c <= i))
      (ensures (length (unique__loop s i c) <= length s))
      (decreases (length s - i))
let rec lemma__unique__length__loop s i c =
   if i < length s then
      let a = index s i in
      let c' =
         if Flutterbye.Seq.Mem.mem a c then
            c
         else
            append c (create 1 a) in
      lemma__unique__length__loop s (i + 1) c'
   else
      ()

abstract val lemma__unique__length:
   s:seq 'a
   -> Lemma
      (requires (True))
      (ensures (length (unique s) <= length s))
let lemma__unique__length s =
   lemma__unique__length__loop s 0 createEmpty

private val lemma__unique__mem__loop:
   // input sequence
   s:seq 'a
   // index of element being examined
   -> i:nat{i <= length s}
   // accumulator; in this case, the output set.
   -> c:seq 'a{unique_t c}
   -> x:'a
   -> Lemma
      (requires
         (((i = 0) ==> (FStar.Seq.equal c createEmpty))
         /\ (Flutterbye.Seq.Mem.mem_t x c <==>
               Flutterbye.Seq.Mem.mem_t x (slice s 0 i))))
      (ensures
         (Flutterbye.Seq.Mem.mem_t x (unique__loop s i c) <==>
            Flutterbye.Seq.Mem.mem_t x s))
      (decreases (length s - i))
let rec lemma__unique__mem__loop s i c x =
   if i < length s then
      let a = index s i in
      (if Flutterbye.Seq.Mem.mem a c then
         let c' = c in
         lemma__unique__mem__loop s (i + 1) c' x
      else
         let c' = append c (create 1 a) in
         let p_1 = Flutterbye.Seq.Mem.mem_t a c' in
         let p_2 = Flutterbye.Seq.Mem.mem_t a (slice s 0 (i + 1)) in
         Flutterbye.Seq.Mem.lemma__slice_2 a s;
         assert (p_1 ==> p_2);
         Flutterbye.Seq.Mem.lemma__append a c (create 1 a);
         assert (Flutterbye.Seq.Mem.mem_t a c');
         assert (p_2 ==> p_1);
         lemma__unique__mem__loop s (i + 1) c' x)
   else
      ()

// todo: are there disadvantages to combining the two `lemma__unique...` lemmas
// given that one needs an additional free variable?
abstract val lemma__unique__mem:
   x:'a
   -> s:seq 'a
   -> Lemma
      (requires (True))
      (ensures
         (Flutterbye.Seq.Mem.mem_t x (unique s) <==>
            Flutterbye.Seq.Mem.mem_t x s))
let lemma__unique__mem x s =
   lemma__unique__mem__loop s 0 createEmpty x
