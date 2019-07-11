var gulp = require('gulp');
var exec = require('child_process').exec;
var compileTypescript = require('gulp-typescript');
// var tslint = require('gulp-tslint');
var shell = require('gulp-shell');
var watch = require('gulp-watch');
var sourcemaps = require('gulp-sourcemaps');
var tsProjectGoals = compileTypescript.createProject('./tsconfig.json', {out: 'goals.js'});
var tsProjectLtacProf = compileTypescript.createProject('./tsconfig.json', {out: 'ltacprof.js'});
var path = require('path');
var util = require('util');

gulp.task('copy-html', function() {
    return gulp.src('./src/**/*.{css,html}')
        .pipe(gulp.dest(tsProjectGoals.options.outDir));
});
gulp.task('compile-goals-ts', function() {
    var result = gulp.src(['./src/goals/**/*.ts'])
        .pipe(sourcemaps.init())
        .pipe(tsProjectGoals());
    return result.js
        // .pipe(sourcemaps.write("."))
        .pipe(sourcemaps.write({sourceRoot: "/html_views"}))
        // .pipe(sourcemaps.write('.', {
        //     mapSources: function (sourcePath) {
        //         console.log(sourcePath);
        //         return sourcePath;
        //     }
        // }))
        .pipe(gulp.dest(tsProjectGoals.options.outDir + '/goals/'));
});
gulp.task('compile-ltacprof-ts', function() {
    var result = gulp.src(['./src/ltacprof/**/*.ts'])
        .pipe(sourcemaps.init())
        .pipe(tsProjectLtacProf())
    return result.js
        // .pipe(sourcemaps.write("."))
        .pipe(sourcemaps.write({sourceRoot: "/html_views"}))
        .pipe(gulp.dest(tsProjectLtacProf.options.outDir + '/ltacprof/'));
});

gulp.task('jquery', function() {
    return gulp.src('./jquery/**/*.{js,css,png}')
        .pipe(gulp.dest(tsProjectGoals.options.outDir + '/jquery/'));
});


// gulp.task('compile-ts', shell.task(['npm run compile --loglevel silent']));

// Watch Files For Changes
gulp.task('watch-html', function() {
    gulp.watch('src/**/*.{html,css}', ['copy-html']);
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
gulp.task('build', ['compile-goals-ts', 'compile-ltacprof-ts', 'copy-html', 'jquery']);
gulp.task('watch', ['watch-html']);
gulp.task('default', ['build', 'watch']);

