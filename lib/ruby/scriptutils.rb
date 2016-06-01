# $legal:619:
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
# ,$

require 'pathname'

module ScriptUtils

   def which(exe_name)
      path_name = `which #{exe_name}`.strip
      if path_name == '' then
         nil
      else
         Pathname.new(path_name)
      end
   end
   module_function :which

end

