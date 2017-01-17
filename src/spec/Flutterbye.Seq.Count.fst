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

module Flutterbye.Seq.Count
open FStar.Seq
open Flutterbye.Seq.Filter

val count:
      #t:Type
   -> f:(t -> Tot bool)
   -> s:seq t
   -> Tot (n:nat{n <= length s})
let count #t f s =
   length (filter f s)

abstract val append_lemma:
   #t:Type
   -> s_1:seq t
   -> s_2:seq t
   -> f:(t -> Tot bool)
   -> Lemma
      (requires (True))
      (ensures (count f s_1 + count f s_2 = count f (append s_1 s_2)))
let append_lemma #t s_1 s_2 f =
   let s' = append s_1 s_2 in
   assert (equal (slice s' 0 (length s_1)) s_1);
   assert (equal (slice s' (length s_1) (length s')) s_2);
   admit ()
