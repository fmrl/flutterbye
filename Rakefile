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

require "pathname"

# repository root is the directory that contains the rakefile.
prefix = Pathname.new(Dir.pwd)
$LOAD_PATH.unshift prefix.join('lib/ruby').to_s

require "fileutils"

has_rubrstmp = true
begin
   require "rubrstmp/rake_tasks"
rescue LoadError
   has_rubrstmp = false
   puts "warning: i was unable to find rubrstmp; related targets will be unavailable." 
end

require "rake/fstar"
require "rake/madoko"
require "rake/npm"
require "scriptutils"

MADOKO_ROOT = Pathname.new "src/doc/madoko"
directory MADOKO_ROOT

Rake::FStar.module_path "src/spec"
Rake::FStar.FSTAR = "./submodules/FStar/bin/fstar.exe"
Rake::FStar.SMT = "./submodules/z3/build/z3#{ScriptUtils.exe_ext}"

task default: [:verify]
desc "verify sources"
task :verify => %w[fstar:verify]

if Npm.has? then
   Rake::Madoko.find MADOKO_ROOT do |p|
      # `p` is relative to `src_doc`.
      MADOKO_ROOT.join(p.dirname.join("out"))
   end
   desc "generate all documentation"
   task :docs => "madoko:generate"
else
   puts 'warning: i was unable to find node.js; madoko-related targets will be unavailable.'
end

if has_rubrstmp then
   namespace :rubrstmp do
      exclude "LICENSE"
      exclude "NOTICE"
      exclude "README.md"
      exclude ".git/*"
      exclude "bin/*"
      exclude "node_modules/*"
      exclude "submodules/*"
      exclude "vendor/*"
      exclude "*.dic"
      exclude "*.json"
      exclude "*.mdk"
      file_keywords \
         "legal" => "NOTICE",
         "vim" => "etc/rubrstmp/vim/default",
         "vim-rb" => "etc/rubrstmp/vim/ruby",
         "vim-fst" => "etc/rubrstmp/vim/fstar"
   end
end

namespace :debug do
   desc "list all tasks (including file tasks)"
   task :ls_tasks do |t, args|
      STDOUT.write Rake::Task.tasks.join("\n")
      STDOUT.flush
   end
end

# $vim-rb:31: vim:set sts=3 sw=3 et ft=ruby:,$



