# $legal:598:
# 
# Copyright 2015 Michael Lowell Roberts
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
# ,$

require_relative "rake/fstar.rb"
require "rubrstmp/rake_tasks"

Rake::FStar.generate_tasks("src/root.fst")

task default: %w[verify]

namespace :rubrstmp do
   exclude "LICENSE"
   exclude "NOTICE"
   exclude "README.md"
   exclude "_vendor/*"
   exclude "bin/*"
   file_keywords \
      "legal" => "NOTICE",
      "vim" => "etc/rubrstmp/vim/default",
      "vim-rb" => "etc/rubrstmp/vim/ruby",
      "vim-fst" => "etc/rubrstmp/vim/fstar"
end

# $vim-rb:31: vim:set sts=3 sw=3 et ft=ruby:,$



