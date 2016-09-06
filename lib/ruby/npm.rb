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

require "scriptutils"

module Npm
   
   module_function
   def has?
      Npm._which
      @has
   end

   module_function
   def which
      Npm._which
      if not @has then
         raise 'i can\'t which npm in your search path. please make sure node.js is installed correctly.'
      else
         @which.to_s
      end
   end

   module_function
   def root
      npm = Npm.which
      Pathname.new `#{npm} root`.strip
   end

   module_function
   def install
      npm = Npm.which
      if not Dir.exists? Npm.root then
         yield "#{npm} install"
      end
   end

   module_function
   def run(script, args=nil)
      npm = Npm.which
      if args == nil then
         yield "#{npm} run #{script}"
      else
         yield "#{npm} run #{script} -- #{args}"
      end
   end

   private

   module_function
   def _which
      if @has == nil
         @which = ScriptUtils.which 'npm'
         @has = @which != nil
      end
      return nil
   end

end

