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

require "pathname"

module Rake::FStar
   
   class << self
      include Rake::DSL

      def home_dir
         @home_dir ||= find_home_dir
      end

      def exe_path
         @exe_path ||= find_exe_path(self.home_dir)
      end

      def lib_path
         @lib_path ||= self.home_dir.join("lib")
      end

      def generate_tasks(files)
         task :verify => files do |t|
            sh "jdepp -a -Dfstar=#{self.lib_path} #{t.prerequisites.join(" ")} -- #{self.exe_path}"
         end
      end

      private

      def find_home_dir
         if ENV["FSTAR_HOME"].nil? then
            raise "i was unable to find the F* home directory; please set the FSTAR_HOME environment variable to the correct path (currently unassigned)."
         end
         home_dir = Pathname.new(ENV["FSTAR_HOME"])
         if not home_dir.exist? then
            raise "i was unable to find the F* home directory; please set the FSTAR_HOME environment variable to the correct path (currently \#{home_dir.to_s}\")"
         end
         home_dir
      end

      def find_exe_path(home_dir)
         pe = home_dir.join("bin/fstar.exe")
         elf = home_dir.join("bin/fstar")
         if pe.exist? then
            pe
         elsif elf.exist? then
            elf
         else
            raise "i was unable to find the F* executable (either \"#{pe.to_s}\" or \"#{elf.to_s}\"). is FSTAR_HOME (#{fstar_home.to_s}) set to the correct path?"
         end
      end

   end

end

# $vim-rb:31: vim:set sts=3 sw=3 et ft=ruby:,$
