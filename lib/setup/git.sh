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

# git repository setup script-- destructive and therefore 
# normally only used with vagrant provisioning.

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

self=$(basename $0)
pwd=$(readlink -e $(pwd))

git clean -fdx -e Vagrantfile -e .vagrant
rm -rf vendor

if [ "$(git config core.eol)" != "lf" ]; then
   echo "$self: resetting eol configuration in git repository '$(pwd)'..."
   git config core.eol lf
   git config core.autocrlf input
   git reset --hard
   git checkout-index --force --all
else
   echo "$self: the eol configuration in git repository '$(pwd)' appears correct."
fi
