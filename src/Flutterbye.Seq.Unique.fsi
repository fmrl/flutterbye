(*--build-config
   options:--admit_fsi FStar.Seq;
   other-files:seq.fsi
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

module Flutterbye.Seq.Unique
   open FStar.Seq

   type Unique: #a:Type -> s:seq a -> Type

   val unique: (s:seq 'a) -> Tot bool

   val lemma__reveal:
      s:seq 'a
      -> Lemma
         (requires (Unique s))
         (ensures
            (0 = length s
            \/ (forall (i:nat) (j:nat).
                  i < length s
                  && j < length s
                  && index s j = index s i
                  ==>
                     j == i)))

   val lemma__unique:
      s:seq 'a
      -> Lemma
         (requires (True))
         (ensures (unique s <==> Unique s))
         // todo: need pattern

   val lemma__empty: s:seq 'a -> Lemma
      (requires (True))
      (ensures (Eq createEmpty s ==> Unique s))
      // todo: need pattern
