#!/usr/bin/env ruby

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

require "rbconfig"

def say(s)
   puts "setup.rb: #{s}"
end

host_os = RbConfig::CONFIG['host_os']
say "platform reported as `#{host_os}`."
if host_os =~ /mswin|msys|mingw|bccwin|wince|emc/
   # file mode changes can cause havok with git on windows.
   say "instructing git to ignore file mode changes..."
   STDOUT.write `git config --local core.fileMode false 2>&1`
end

# todo: detect whether bundler is available.
say "performing bundler setup..."
STDOUT.write `bundle install --path vendor/bundle 2>&1`

say "done."

# $vim-rb:31: vim:set sts=3 sw=3 et ft=ruby:,$
