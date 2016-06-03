# $legal$

require "rake/dsl_definition"
require "scriptutils"

module Rake::FStar
   self.extend Rake::DSL
   
   module_function
   def FSTAR; @fstar end
   def FSTAR= s
      @fstar = Pathname.new(s.to_s) 
   end

   module_function
   def FSTARFLAGS; @fstarflags end
   def FSTARFLAGS= s; @fstarflags = s end
   
   module_function
   def FSTARSMT; @fstarsmt end
   def FSTARSMT= s
      @fstarsmt = Pathname.new(s.to_s) 
   end
   
   module_function
   def verify(file_list)
      namespace :fstar do
         desc "verify all f* sources"
         task :verify => file_list do |t, args|
            ScriptUtils.raise_if_not_executable @fstar
            ScriptUtils.raise_if_not_executable @fstarsmt
            smt = @fstarsmt.to_s
            # on Windows, unless Z3's path is normalized, F* will fail.
            if ScriptUtils.is_windows? then
               smt = smt.gsub(File::SEPARATOR,
     File::ALT_SEPARATOR || File::SEPARATOR)
            end
            sh "#{@fstar.to_s} --smt #{smt} #{@fstarflags} #{t.prerequisites.join(" ")}"
         end
         desc "list f* sources in project"
         task :ls do |t|
            puts "#{file_list.to_a.join("\n")}"
            STDOUT.flush
         end
      end
   end
   
end