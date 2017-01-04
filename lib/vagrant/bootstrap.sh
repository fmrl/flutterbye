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

APT_PACKAGES="git build-essential mono-devel fsharp ruby python opam m4 libgmp-dev"

# this solves a problem with upgrading the `grub-pc` package. see
# https://github.com/mitchellh/vagrant/issues/289
echo "set grub-pc/install_devices /dev/sda" | debconf-communicate

# at the time of this commit, mono is broken in debian due to changes
# in how certificates are obtained. we need to obtian mono directly from
# the source if we want to use tools such as nuget (required for F*).
# from http://www.mono-project.com/docs/getting-started/install/linux/#debian-ubuntu-and-derivatives
apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF
echo "deb http://download.mono-project.com/repo/debian wheezy main" | tee /etc/apt/sources.list.d/mono-xamarin.list
echo "deb http://download.mono-project.com/repo/debian wheezy-libjpeg62-compat main" | tee -a /etc/apt/sources.list.d/mono-xamarin.list

apt-get update && apt-get -y dist-upgrade
apt-get -y install $APT_PACKAGES

gem install bundler

cd /vagrant

# this step is only recommended if you're using vagrant.
sudo -u vagrant -- bundle install --system

sudo -u vagrant -- /bin/sh lib/vagrant/setup-opam.sh  
sudo -u vagrant -- /bin/sh lib/vagrant/setup.sh  

