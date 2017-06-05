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

# submodule setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

gitroot=$(git rev-parse --show-toplevel)

git submodule init
git submodule update

# this shouldn't do anything if we're using vagrant (see `/scripts/setup/vagrant.sh`).
if [ "x$1" == "x--vagrant" ]; then
   git submodule foreach '$SHELL ../../scripts/setup/git.sh'
fi

$SHELL $gitroot/scripts/setup/z3.sh build
$SHELL $gitroot/scripts/setup/fstar.sh
$SHELL $gitroot/scripts/setup/ivy.sh
