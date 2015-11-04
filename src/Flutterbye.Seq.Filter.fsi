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

module Flutterbye.Seq.Filter
   open FStar.Seq
   open Flutterbye.Seq.Mem

   val filter:
      ('a -> Tot bool)
         // predicate; if false, then the element is discarded from the
         // sequence.
      -> seq 'a // input sequence
      -> Tot (seq 'a) // output sequence

   val lemma__predicate:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> i: nat{i < length (filter p s)}
      -> Lemma
         (requires (True))
         (ensures (p (index (filter p s) i)))
         [SMTPat (index (filter p s) i)]

   val lemma__length:
      p: ('a -> Tot bool)
      -> s: seq 'a
      -> Lemma
         (requires (True))
         (ensures (length (filter p s) <= length s))
         [SMTPat (length (filter p s))]

   val lemma__preserves_mem:
      p: ('a -> Tot bool) ->
      s: seq 'a ->
      Lemma
         (requires (True))
         (ensures
            (forall i.
               0 <= i && i < length (filter p s)
               ==> mem s (index (filter p s) i)))
