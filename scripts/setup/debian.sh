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

# debian/ubuntu superuser setup script

# show what's happening.
set -x
# exit on any unobserved failure.
set -e

APT_PACKAGES="vim-tiny git build-essential mono-devel mono-complete mono-dbg ca-certificates-mono fsharp ruby python-dev python-pip opam m4 libgmp-dev graphviz-dev"

# compare version numbers (from https://stackoverflow.com/questions/4023830/how-compare-two-strings-in-dot-separated-version-format-in-bash#4024263)
ver_lte() {
    [  "$1" = "`echo -e "$1\n$2" | sort -V | head -n1`" ]
}

ver_lt() {
    [ "$1" = "$2" ] && return 1 || ver_lte $1 $2
}

# at the time of this commit, mono is broken in debian due to changes
# in how certificates are obtained. we need to obtian mono directly from
# the source if we want to use tools such as nuget (required for F*).
# from http://www.mono-project.com/docs/getting-started/install/linux/#debian-ubuntu-and-derivatives
apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF
echo "deb http://download.mono-project.com/repo/debian jessie main" | tee /etc/apt/sources.list.d/mono-xamarin.list

# the following workaround saves us from a long-standing concurrency bug in `apt` that
# i have observed when using vagrant on windows systems.
# see https://stackoverflow.com/questions/15505775/debian-apt-packages-hash-sum-mismatch
# for more details. at some point, this will not be needed but that seems like a long
# ways off still.
rm -rf /var/lib/apt/lists/*
apt-get clean
apt_fix_path=/etc/apt/apt.conf.d/99fixbadproxy
echo "Acquire::http::Pipeline-Depth 0;" > $apt_fix_path
echo "Acquire::http::No-Cache true;" >> $apt_fix_path
echo "Acquire::BrokenProxy true;" >> $apt_fix_path

# versions of ubuntu earlier than xenial (16.04) ship with either broken
# or uselessly outdated versions of opam.
lsb_id=$(lsb_release -si)
lsb_ver=$(lsb_release -sr)
if [ "xUbuntu" = "x$lsb_id" ]; then
   if ver_lt $lsb_ver 16.04; then
      # container-based distributions might not have `add-apt-repository`
      # installed by default. older versions of ubuntu (e.g. precise)
      # packaged this utility with `python-software-properties`. it has since
      # been moved to `software-properties-common` but there's no harm in
      # installing both.
      apt-get update
      apt-get -y install software-properties-common python-software-properties
      # the ubuntu `opam` packages are too old to be useful to us.
      add-apt-repository -y ppa:avsm/ppa
   fi
fi

# install all of the packages specified at the top of this script.
apt-get update
apt-get -y install $APT_PACKAGES

# let's install security updates to be safe.
apt-get -y install unattended-upgrades
unattended-upgrade

gem install bundler

