(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi Flutterbye.Seq.Mem --admit_fsi Flutterbye.Seq.Unique;
   other-files:seq.fsi set.fsi Flutterbye.Seq.Mem.fsi Flutterbye.Seq.Unique.fsi Flutterbye.Seq.Disjoint.fsi
--*)

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

module Flutterbye.Seq.Disjoint
open FStar.Seq
open FStar.Set
open Flutterbye.Seq.Unique

type Disjoint (#a:Type) (s_1:seq a) (s_2:seq a) =
   FStar.Set.Equal empty (intersect (to_set (unique s_1)) (to_set (unique s_2)))

let lemma__intersect s_1 s_2 =
   ()

let lemma__mem x s_1 s_2 =
   let t_1 = to_set (unique s_1) in
   (Flutterbye.Seq.Unique.lemma__unique__mem x (s_1);
   Flutterbye.Seq.Unique.lemma__to_set x (unique s_1);
   assert (mem x t_1 <==> Flutterbye.Seq.Mem.mem x s_1));
   let t_2 = to_set (unique s_2) in
   (Flutterbye.Seq.Unique.lemma__unique__mem x (s_2);
   Flutterbye.Seq.Unique.lemma__to_set x (unique s_2);
   assert (mem x t_2 <==> Flutterbye.Seq.Mem.mem x s_2));
   if mem x t_1 then
      (FStar.Set.mem_intersect x t_1 t_2;
      assert (not (mem x t_2)))
   else if mem x t_2 then
      (FStar.Set.mem_intersect x t_1 t_2;
      assert (not (mem x t_1)))
   else
      ()
