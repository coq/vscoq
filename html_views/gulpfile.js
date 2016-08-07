var gulp = require('gulp');
var exec = require('child_process').exec;
var compileTypescript = require('gulp-typescript');
// var tslint = require('gulp-tslint');
var shell = require('gulp-shell');
var watch = require('gulp-watch');
var tsProject = compileTypescript.createProject('./tsconfig.json');

var util = require('util');

gulp.task('copy-html', function() {
    return gulp.src('./src/**/*.html')
        .pipe(gulp.dest(tsProject.options.outDir));
});
gulp.task('compile-goals-ts', function() {
    return gulp.src(['./src/goals/**/*.ts'])
        .pipe(compileTypescript({target: 'es6', module: 'none', outFile: 'goals.js'}))
        .pipe(gulp.dest(tsProject.options.outDir + '/goals/'));
});
gulp.task('compile-ltacprof-ts', function() {
    return gulp.src(['./src/ltacprof/**/*.ts'])
        .pipe(compileTypescript({target: 'es6', out: 'ltacprof.js'}))
        .pipe(gulp.dest(tsProject.options.outDir + '/ltacprof/'));
});
// gulp.task('jquery', function() {
//     return gulp.src('./src/HtmlView/jquery/**/*.{js,css,png}')
//         .pipe(gulp.dest(tsProject.options.outDir + '/src/HtmlView/jquery/'));
// });


// gulp.task('compile-ts', shell.task(['npm run compile --loglevel silent']));

// Watch Files For Changes
gulp.task('watch-html', function() {
    gulp.watch('src/**/*.html', ['copy-html']);
    gulp.watch(['./src/goals/**/*.ts'], ['compile-goals-ts']);
    gulp.watch(['./src/ltacprof/**/*.ts'], ['compile-ltacprof-ts']);
    // gulp.watch('./src/HtmlView/jquery/**/*.{js,css,png}', ['jquery']);
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
gulp.task('build', ['compile-goals-ts', 'compile-ltacprof-ts', 'copy-html']);
gulp.task('watch', ['watch-html']);
gulp.task('default', ['build', 'watch']);

