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

# userland setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

$SHELL scripts/setup/opam.sh
$SHELL scripts/setup/bundler.sh

if [ "x$1" = "x--vagrant" ] && ! grep -q 'cd /vagrant' $HOME/.profile; then
   echo 'cd /vagrant' >> $HOME/.profile
   echo 'eval "export PATH=$HOME/.local/bin:$PATH"' >> $HOME/.profile
   echo 'eval "$(sh /vagrant/scripts/setup/z3.sh env)"' >> $HOME/.profile
fi
