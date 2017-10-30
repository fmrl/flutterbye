# -*- mode: ruby -*-
# vi: set ft=ruby :

# Vagrant configuration (https://docs.vagrantup.com)

Vagrant.configure("2") do |config|

   # the virtualbox provider will always work, so it's the default.
   config.vm.provider "virtualbox" do |vb, override|
      #vb.gui = true
      vb.memory = "2048"
      override.vm.box = "debian/contrib-jessie64"
      # the (`vagrant-vbguest`)[https://github.com/dotless-de/vagrant-vbguest]
      # plugin can fail when the guest tools installation prompts for
      # confirmation, so we need to ensure it's not interactive.
      if Vagrant.has_plugin? "vagrant-vbguest" then
         config.vbguest.installer_arguments = "--nox11 -- --force"
      end
   end

   # docker appears to be an unpopular vagrant provider (the most popular box
   # has only 184 downloads at the moment this sentence is being written!). i
   # prefer the docker provider to more heavyweight virtualization providers,
   # however, but the docker provider seems to only work properly on linux.
   config.vm.provider "docker" do |d, override|
      # NOTE: you may need to manually pull this box before issuing a
      #`vagrant up --provider=docker` on older versions of vagrant.
      # NOTE: the docker image doesn't seem to work with X11 forwarding. :(
      override.vm.box = "tknerr/baseimage-ubuntu-16.04"
   end

   config.ssh.forward_x11 = true

   config.vm.provision "shell", inline: <<-SHELL
      /bin/sh /vagrant/lib/flutterbye/setup/vagrant.sh
   SHELL

end
