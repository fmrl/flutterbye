# $legal:309:
# 
# This work is licensed under the Creative Commons
# Attribution-NonCommercial-ShareAlike 4.0 International
# License. To view a copy of this license, visit
# http://creativecommons.org/licenses/by-nc-sa/4.0/
# or send a letter to:
# 
# Creative Commons
# PO Box 1866
# Mountain View, CA 94042
# USA
# 
# ,$

require_relative "rake/fstar.rb"
require "rubrstmp/rake_tasks"

Rake::FStar.generate_tasks("src/root.fst")

task default: %w[verify]

namespace :rubrstmp do
   exclude "LICENSE"
   exclude "README.md"
   exclude "_vendor/*"
   exclude "bin/*"
   file_keywords \
      "legal" => "LICENSE",
      "vim" => "etc/rubrstmp/vim/default",
      "vim-rb" => "etc/rubrstmp/vim/ruby",
      "vim-fst" => "etc/rubrstmp/vim/fstar"
end

# $vim-rb:31: vim:set sts=3 sw=3 et ft=ruby:,$



