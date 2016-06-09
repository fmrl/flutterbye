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

module Flutterbye.Seq.Disjoint
open FStar.Seq
open FStar.Set
open Flutterbye.Seq.Unique

type disjoint_t (#a:Type) (s_1:seq a) (s_2:seq a) =
   FStar.Set.equal empty (intersect (to_set (unique s_1)) (to_set (unique s_2)))

abstract val lemma__intersect:
   s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires
         (FStar.Set.equal
            empty
            (intersect
               (to_set (unique s_1))
               (to_set (unique s_2)))))
      (ensures (disjoint_t s_1 s_2))
let lemma__intersect s_1 s_2 =
   ()

abstract val lemma__mem:
x:'a
-> s_1:seq 'a
-> s_2:seq 'a
-> Lemma
   (requires (disjoint_t s_1 s_2))
   (ensures
      ((Flutterbye.Seq.Mem.mem_t x s_1 \/ Flutterbye.Seq.Mem.mem_t x s_2) <==>
         ((Flutterbye.Seq.Mem.mem_t x s_1 <==>
            ~ (Flutterbye.Seq.Mem.mem_t x s_2)))))
let lemma__mem x s_1 s_2 =
   let t_1 = to_set (unique s_1) in
   (Flutterbye.Seq.Unique.lemma__unique__mem x (s_1);
   Flutterbye.Seq.Unique.lemma__to_set x (unique s_1);
   assert (b2t (mem x t_1) <==> Flutterbye.Seq.Mem.mem_t x s_1));
   let t_2 = to_set (unique s_2) in
   (Flutterbye.Seq.Unique.lemma__unique__mem x (s_2);
   Flutterbye.Seq.Unique.lemma__to_set x (unique s_2);
   assert (b2t (mem x t_2) <==> Flutterbye.Seq.Mem.mem_t x s_2));
   if mem x t_1 then
      (FStar.Set.mem_intersect x t_1 t_2;
      assert (not (mem x t_2)))
   else if mem x t_2 then
      (FStar.Set.mem_intersect x t_1 t_2;
      assert (not (mem x t_1)))
   else
      ()
