# $legal$

require "rake/dsl_definition"
require "scriptutils"

module Rake::FStar
   self.extend Rake::DSL
   
   module_function
   def FSTAR
      @fstar ||= Pathname.new "./submodules/FStar/bin/fstar.exe"
      return @fstar 
   end
   def FSTAR= s
      @fstar = Pathname.new(s.to_s) 
   end

   module_function
   def FSTARFLAGS
      @fstarflags ||= "--universes"
      return @fstarflags  
   end
   def FSTARFLAGS= s; @fstarflags = s end
   
   module_function
   def FSTARSMT
      @fstarsmt ||= Pathname.new "./submodules/z3/build/z3#{ScriptUtils.exe_ext}"
      return @fstarsmt
   end
   def FSTARSMT= s
      @fstarsmt = Pathname.new(s.to_s) 
   end
   
   module_function
   def verify(file_list)
      namespace :fstar do
         desc "verify all f* sources"
         task :verify => file_list do |t, args|
            fstar = Rake::FStar.FSTAR
            ScriptUtils.raise_if_not_executable fstar
            fstarsmt = Rake::FStar.FSTARSMT
            ScriptUtils.raise_if_not_executable fstarsmt
            fstarflags = Rake::FStar.FSTARFLAGS
            # on Windows, unless Z3's path is normalized, F* will fail.
            fstarsmt_s = fstarsmt.to_s
            if ScriptUtils.is_windows? then
               fstarsmt_s = fstarsmt_s.gsub(File::SEPARATOR,
     File::ALT_SEPARATOR || File::SEPARATOR)
            end
            sh "#{fstar.to_s} --smt #{fstarsmt_s} #{fstarflags} #{t.prerequisites.join(" ")}"
         end
         desc "list f* sources in project"
         task :ls do |t|
            puts "#{file_list.to_a.join("\n")}"
            STDOUT.flush
         end
      end
   end
   
end