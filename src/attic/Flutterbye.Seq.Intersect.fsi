(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi Flutterbye.Seq.Mem;
   other-files:seq.fsi Flutterbye.Seq.Mem.fsi
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

module Flutterbye.Seq.Intersect
open FStar.Seq
open Flutterbye.Seq.Mem

type Intersect: #a:Type -> s_i:seq a -> s_1:seq a -> s_2:seq a -> Type

val insersect:
   s_1:seq 'a
   -> s_2:seq 'a
   -> Tot (s_i:seq 'a{Intersect s_i s_1 s_2})

val lemma__empty:
   s_1:seq 'a
   -> s_2:seq 'a
   -> Lemma
      (requires (length s_1 = 0 || length s_2 = 0))
      (ensures (Intersect createEmpty s_1 s_2))
