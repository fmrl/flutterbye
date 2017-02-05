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

# userspace setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

OCAML_VERSION="4.02.3"
OPAM_PACKAGES="ocamlfind batteries stdint zarith yojson pprint"

# setup opam
opam init --comp $OCAML_VERSION --auto-setup
eval $(opam config env)
opam install -y $OPAM_PACKAGES

# this shouldn't do anything if we're using vagrant (see `/scripts/setup/vagrant.sh`).
if [ "$(pwd)" != "/vagrant" ] && [ "$(whoami)" != "vagrant" ]; then
   bundle install --path vendor/bundle
else
   bundle install --system
fi
