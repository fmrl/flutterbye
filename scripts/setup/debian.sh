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

# debian setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

APT_PACKAGES="vim-tiny git build-essential mono-devel fsharp ruby python opam m4 libgmp-dev"

# compare version numbers (from https://stackoverflow.com/questions/4023830/how-compare-two-strings-in-dot-separated-version-format-in-bash#4024263)
ver_lte() {
    [  "$1" = "`echo -e "$1\n$2" | sort -V | head -n1`" ]
}

# `apt-get clean` saves us from a long-standing concurrency bug in `apt`.
# see https://askubuntu.com/questions/41605/trouble-downloading-packages-list-due-to-a-hash-sum-mismatch-error/
# for more details.
apt-get clean
sudo rm -rf /var/lib/apt/lists/*
sudo apt-get update -o Acquire::CompressionTypes::Order::=gz

# let's get security updates and nothing more, to be safe.
apt-get update
apt-get -y install unattended-upgrades
unattended-upgrade

# at the time of this commit, mono is broken in debian due to changes
# in how certificates are obtained. we need to obtian mono directly from
# the source if we want to use tools such as nuget (required for F*).
# from http://www.mono-project.com/docs/getting-started/install/linux/#debian-ubuntu-and-derivatives
apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF
echo "deb http://download.mono-project.com/repo/debian wheezy main" | tee /etc/apt/sources.list.d/mono-xamarin.list

lsb_id=$(lsb_release -si)
if [ "xUbuntu" = "x$lsb_id" ]; then
   # container-based distributions might not have `add-apt-repository`
   # installed by default. older versions of ubuntu (e.g. precise)
   # packaged this utility with `python-software-properties`. it has since
   # been moved to `software-properties-common` but there's no harm in
   # installing both.
   apt-get -y install software-properties-common python-software-properties
   # the ubuntu `opam` packages are too old to be useful to us.
   add-apt-repository -y ppa:avsm/ppa
else
   # debian requires a special build of `libgdiplus`.
   echo "deb http://download.mono-project.com/repo/debian wheezy-libjpeg62-compat main" | tee -a /etc/apt/sources.list.d/mono-xamarin.list
fi

apt-get update && apt-get -y upgrade
apt-get -y install $APT_PACKAGES

gem install bundler

