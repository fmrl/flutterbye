(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi Flutterbye.Seq.Unique;
   other-files:seq.fsi Flutterbye.Seq.Unique.fsi Flutterbye.Schedule.Core.fsi
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

module Flutterbye.Schedule.Core
   open FStar
   open Flutterbye

   type seq = FStar.Seq.seq
   type Unique = Flutterbye.Seq.Unique.Unique

   type Name = nat

   type Effect =
      | Spawn:(name:Name -> Effect)
      | Message:Effect

   type Schedule = seq Effect

   let empty =
      Seq.createEmpty

   let length s =
      Seq.length s

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
