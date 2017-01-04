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

set -x

# exit on any unobserved failure.
set -e

git submodule init
git submodule update
/bin/sh lib/vagrant/git-clean-all.sh

/bin/sh lib/vagrant/git-reset-eol.sh
git submodule foreach '/bin/sh ../../lib/vagrant/git-reset-eol.sh'

/bin/sh lib/vagrant/build-z3.sh
/bin/sh lib/vagrant/build-fstar.sh

# this shouldn't do anything if we're using vagrant (see `bootstrap.sh`).
if [ "$(pwd)" != "/vagrant" ] && [ "$(whoami)" != "vagrant" ]; then
   bundle install --path vendor/bundle 
fi
