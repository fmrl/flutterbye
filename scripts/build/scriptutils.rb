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

require "open3"
require "pathname"
require "rbconfig"

module ScriptUtils

   module_function
   def which(exe_name)
      if ScriptUtils.is_windows? then
         cmd = "cmd.exe /c where #{exe_name}"
         # where is a little chatty on stderr, so we use popen3 to suppress stderr.
         output = Open3.popen3(cmd) do |stdin, stdout, stderr, wait_thr|
            stdout.read
         end
         lines = output.each_line.to_a
         if lines.length == 0 then
            return nil 
         end
         path = lines[0].strip
         if path == '' then
            return nil
         end
         return Pathname.new(path)
      else
         path = `which #{exe_name}`.strip
         if $? != 0 or path == '' then
            return nil
         else
            return Pathname.new(path)
         end
      end
   end
   
   module_function
   def is_windows?
      RbConfig::CONFIG['host_os'] =~ /mswin|mingw/
   end

   module_function
   def raise_if_nonexistant(pathn)
      if not pathn.exist? then
         raise "`#{pathn.to_s}` does not (yet) exist."
      end
   end

   module_function
   def raise_if_not_executable(pathn)
      ScriptUtils.raise_if_nonexistant(pathn)
      if not pathn.executable? then
         raise "`#{pathn.to_s}` is not executable."
      end
   end
   
   module_function
   def exe_ext
      if ScriptUtils.is_windows? then
         return ".exe"
      else
         return ""
      end
   end
   
end

