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
      @flags ||= ""
      return @flags
   end

   module_function
   def FLAGS= s; @flags = s end

   module_function
   def Z3RLIMIT
      @z3rlimit ||= nil
      return @z3rlimit
   end

   module_function
   def Z3RLIMIT= s
      @z3rlimit = s
   end

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
            task :verify, :modules, :z3rlimit do |t, args|
               args.with_defaults(:modules => "*", :z3rlimit => @z3rlimit)
               modules = @modules_found.keys.select { |m| File.fnmatch(args[:modules], m, File::FNM_CASEFOLD) }
               # bug: the version of f* that we're using doesn't validate all
               # modules if we pass them all on a single command line.
               #sh (format_command(modules, args[:timeout]))
               modules.each { |m| sh (format_command([m], args[:z3rlimit], "--use_hints")) }
            end

            desc "record f* hints"
            task :record, :modules, :z3rlimit do |t, args|
               args.with_defaults(:modules => "*", :z3rlimit => @z3rlimit)
               modules = @modules_found.keys.select { |m| File.fnmatch(args[:modules], m, File::FNM_CASEFOLD) }
               # bug: the version of f* that we're using doesn't validate all
               # modules if we pass them all on a single command line.
               #sh (format_command(modules, args[:timeout]))
               modules.each { |m| sh (format_command([m], args[:z3rlimit], "--record_hints")) }
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

   def format_command(modules, z3rlimit, extra_flags)
      smt = Rake::FStar.SMT.to_s
      # on Windows, unless Z3's path is normalized, F* will fail.
      if ScriptUtils.is_windows? then
         smt.gsub!("/", "\\")
      end
      if z3rlimit.nil? then
         z3rlimit = ""
      else
         z3rlimit = " --z3rlimit #{z3rlimit.to_s}"
      end
      if extra_flags.nil? then
         extra_flags = ""
      end
      return "#{Rake::FStar.FSTAR.to_s} --smt #{smt} #{z3rlimit} #{Rake::FStar.FLAGS} #{extra_flags} --include #{@include_paths.to_a.map {|p| p.to_s}.sort.join("--include ")} #{modules.sort.map {|m| "#{@modules_found[m]}"}.join(" ")}"
   end
end
