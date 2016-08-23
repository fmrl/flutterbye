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

module Flutterbye.Prelude

// adapted from f* sample code.
// todo: why is this in lib/prims.fst but not ulib/prims.fst?
// it appears to still be in mitls (see StatefulLHAE.fst, line 172),
// which suggests that it is not incompatible with `--universes`
type Let (#a_t:Type) (x:a_t) (body:(y:a_t{y = x} -> Type)) = body x
