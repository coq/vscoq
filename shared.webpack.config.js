//@ts-check
/** @typedef {import('webpack').Configuration} WebpackConfig **/

'use strict';

const path = require("path");
const webpack = require("webpack");
const merge = require('merge-options');

module.exports = 
  function withDefaults(/**@type WebpackConfig*/extConfig) {

    /** @type WebpackConfig */
  const defaultConfig = {
    mode: 'none', // this leaves the source code as close as possible to the original (when packaging we set this to 'production')
    target: 'node', // extensions run in a node context
    //node: {
    //	__dirname: false // leave the __dirname-behaviour intact
    //},
    module: {
      rules: [{
        test: /\.ts$/,
        exclude: /node_modules/,
        use: [{
          // configure TypeScript loader:
          // * enable sources maps for end-to-end source maps
          loader: 'ts-loader',
          options: {
            compilerOptions: {
              "sourceMap": true,
            }
          }
        }]
      }]
    },
    resolve: {
      mainFields: ['module', 'main'],
      extensions: ['.ts', '.js'] // support ts-files and js-files
    }, 
    output: {
      filename: '[name].js',
      path: path.resolve(__dirname, "out"),
      libraryTarget: "commonjs",
      clean: true
    },
    externals: {
      'vscode': 'commonjs vscode', // ignored because it doesn't exist
    },
    plugins: [
      new webpack.ProvidePlugin({
        jQuery: "jquery",
        $: "jquery",
        jquery: "jquery"
      })
    ],
    devtool: 'source-map'
  };
  return merge(defaultConfig, extConfig);
}
