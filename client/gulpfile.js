var gulp = require('gulp');
var exec = require('child_process').exec;
var compileTypescript = require('gulp-typescript');
// var tslint = require('gulp-tslint');
var shell = require('gulp-shell');
var watch = require('gulp-watch');
var tsProject = compileTypescript.createProject('./tsconfig.json');

var util = require('util');

gulp.task('html', function() {
    return gulp.src('./src/HtmlView/*.html')
        .pipe(gulp.dest(tsProject.options.outDir + '/src/HtmlView/'));
});
gulp.task('compile-html-ts', function() {
    return gulp.src('./src/HtmlView/*.ts')
        .pipe(compileTypescript({out: 'controller.js'}))
        .pipe(gulp.dest(tsProject.options.outDir + '/src/HtmlView/'));
});


gulp.task('compile-ts', shell.task(['npm run compile --loglevel silent']));

// Watch Files For Changes
gulp.task('watch-html', function() {
    gulp.watch('src/HtmlView/*.html', ['html']);
    gulp.watch('src/HtmlView/*.ts', ['compile-html-ts']);
});
// gulp.task('watch-ts', function() {
//    gulp.watch('src/*.ts', ['compile-ts']);
//   // tsProject.src()
//   //   .pipe(watch('**/*.ts'))
//   //   .pipe(gulp.dest("compile-ts"));
// });


  // process.stdout.write(util.inspect(tsProject.src(),false,2)+'\n');
  // process.stdout.write("--------------------\n");

// Default Task
gulp.task('build', ['compile-ts', 'compile-html-ts', 'html']);
gulp.task('watch', ['watch-html']);
gulp.task('default', ['build', 'watch']);

