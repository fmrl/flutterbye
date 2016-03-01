var path = require('path');

var globule = require('globule');

var outputPath = 'out';

var mdkTargets = [];
var matches = globule.findMapping('**/*.mdk', { srcBase: 'src/doc', rename: function (s) { return path.join(outputPath, 'doc', path.dirname(s), path.basename(s, '.mdk') + '.html') }});
for (var i = 0; i < matches.length; ++i) {
   var match = matches[i];
   var odir = path.dirname(match.dest);
   // todo: globule returns source files in an array. why?
   var src = match.src[0];
   mdkTargets.push(match.dest);

   directory(odir);
   file(match.dest, [odir, src], { async: true }, function () {
      var cmd = 'madoko --odir=' + odir + ' ' + src;
      jake.logger.log(cmd);
      jake.exec([cmd], { printStdout: !jake.program.opts.quiet, printStderr: !jake.program.opts.quiet });
   });
}
desc('madoko documentation');
task('madoko', mdkTargets);

desc('build everything');
task('default', ['madoko']);

// vim:set sts=3 sw=3 et ft=javascript:
