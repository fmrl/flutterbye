#!/bin/sh

# $legal:613:
#
# Copyright 2016 Michael Lowell Roberts & Microsoft Research
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
#,$

# z3 setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

self=$(basename $0)
target=$(readlink -m submodules/z3/build/z3)

if [ ! -x "$target" ]; then
   echo "$self: i couldn't find the z3 executable; rebuilding..."
   cd submodules/z3
   git clean -fdx
   python scripts/mk_make.py
   cd build && make
else
   echo "$self: i found the z3 executable at '$target'."
fi

