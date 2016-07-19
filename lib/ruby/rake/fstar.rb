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

require "rake/dsl_definition"
require "scriptutils"

module Rake::FStar
   self.extend Rake::DSL

   @modules_found = {}
   @include_paths = Set.new
   
   module_function
   def FSTAR
      @fstar ||= Pathname.new "fstar.exe"
      return @fstar 
   end
   
   module_function
   def FSTAR= s
      @fstar = Pathname.new(s.to_s) 
      ScriptUtils.raise_if_not_executable @fstar
   end

   module_function
   def SMT
      @smt ||= Pathname.new "z3#{ScriptUtils.exe_ext}"
      return @smt
   end

   module_function
   def SMT= s
      @smt = Pathname.new(s.to_s)
      ScriptUtils.raise_if_not_executable @smt
   end

   module_function
   def FLAGS
      @flags ||= "--universes"
      return @flags  
   end

   module_function
   def FLAGS= s; @flags = s end
   
   module_function
   def module_path(dir_path)
      dir_path = Pathname.new(dir_path)
      glob = dir_path.join("**/*.fst").to_s
      if ScriptUtils.is_windows? then
         # Rake::FileList doesn't like Windows-style path separators.
         glob.gsub!("\\", "/")
      end
      files = Rake::FileList[glob]
      
      files.each do |s|
         fp = Pathname.new(s)
         @include_paths << fp.dirname
         @modules_found[fp.basename(".fst")] = fp
      end

      define_tasks
   end

   def define_tasks
      if not Rake::Task.task_defined?("fstar:verify") then
         namespace :fstar do
            desc "verify all F* modules"
            task :verify, :modules do |t, args|
               # todo: i don't quite understand why `args[:modules]` is an array.
               if args[:modules].empty? then                  
                  sh (format_command @modules_found.keys)
               else
                  sh (format_command @modules_found.keys.select { |m| File.fnmatch(args[:modules][0], m) })
               end
            end

            desc "list F* modules found."
            task :ls do |t|
               STDOUT.write \
                  (@modules_found.keys.sort.map do |m|
                     "#{m} (defined in '#{@modules_found[m]}')"
                  end)
                  .join("\n")
               STDOUT.write "\n"
               STDOUT.flush
            end
         end
         if Rake.application.options.trace then
            Rake.application.options.trace_output.write \
               "'fstar:' namespace is now available.\n"
         end
      end
   end

   def format_command(modules)
      smt = Rake::FStar.SMT.to_s
      # on Windows, unless Z3's path is normalized, F* will fail.
      if ScriptUtils.is_windows? then
         smt.gsub!("/", "\\")
      end
      return "#{Rake::FStar.FSTAR.to_s} --smt #{smt} #{Rake::FStar.FLAGS} --include #{@include_paths.to_a.map {|p| p.to_s}.sort.join("--include ")} #{modules.sort.map {|m| "#{@modules_found[m].basename}"}.join(" ")}"
   end
end