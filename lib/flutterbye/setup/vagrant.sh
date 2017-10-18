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

# vagrant bootstrap script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

# this solves a problem with upgrading the `grub-pc` package. see
# https://github.com/mitchellh/vagrant/issues/289
(echo "set grub-pc/install_devices /dev/sda" | debconf-communicate) || true > /dev/null

$SHELL /vagrant/submodules/ivy/scripts/setup/debian.sh

cd /vagrant/submodules/ivy
sudo -H -u vagrant -- $SHELL ./scripts/setup/userland.sh --vagrant
sudo -H -u vagrant -- $SHELL ./scripts/setup/submodules.sh --vagrant

cd /vagrant
