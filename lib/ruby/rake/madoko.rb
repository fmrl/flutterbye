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

require 'rake/dsl_definition'
require 'tmpdir'

require 'rake/npm'


module Rake::Madoko
   self.extend Rake::DSL
   
   module_function
   def find(root)

      namespace :madoko do

         desc "start local madoko editor"
         task :local, [:port] => %w[npm:install] do |t, args|
            args.with_defaults(:port => rand(32767) + 1024) 
            # boo: the --rundir option appears to be broken
            #tmpdir = Dir.mktmpdir
            #Npm.run('exec', "madoko-local -l --port=#{args.port} --rundir=#{tmpdir} #{root}") { |s| sh s }
            Npm.run('madoko-local', "-l --port=#{args.port} #{root}") { |s| sh s }
         end

         # todo: list documentation sources task
         desc "generate madoko documentation"
         task :generate

      end

      Dir.glob(root.join("**/*.mdk")) do |match|
         match = Pathname.new(match)

         odir = yield match.relative_path_from(root)
         html = odir.join("#{match.basename(".mdk")}.html")
         file html => match do |t|
            sh "npm run madoko -- --pdf --odir=#{odir} #{match}"
         end

         pdf = odir.join("#{match.basename(".mdk")}.pdf")
         file pdf => html

         task %[madoko:generate] => [html, pdf]
      end
   end

end

