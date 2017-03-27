# -*- mode: ruby -*-
# vi: set ft=ruby :

# Vagrant configuration (https://docs.vagrantup.com)

Vagrant.configure("2") do |config|

   # the virtualbox provider will always work, so it's the default.
   config.vm.provider "virtualbox" do |vb, override|
      #vb.gui = true
      vb.memory = "2048"
      override.vm.box = "debian/contrib-jessie64"
   end

   # `hashicorp/precise64` hit a roadblock when trying to compile ocaml, so
   # an alternative box with a newer distro needed to be used.
   config.vm.provider "hyperv" do |hyperv, override|
      #hyperv.gui = true
      hyperv.memory = "2048"
      override.vm.box = "nikel/xerus64"
   end

   # docker appears to be an unpopular vagrant provider (the most popular box
   # has only 184 downloads at the moment this sentence is being written!). i
   # prefer the docker provider to more heavyweight virtualization providers,
   # however, but the docker provider seems to only work properly on linux.
   config.vm.provider "docker" do |d, override|
      override.vm.box = "tknerr/baseimage-ubuntu-16.04"
   end

   config.vm.provision "shell", inline: <<-SHELL
      /bin/sh /vagrant/scripts/setup/vagrant.sh
   SHELL

end
