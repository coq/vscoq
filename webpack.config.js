const path = require("path");
const webpack = require("webpack");
const CopyPlugin = require("copy-webpack-plugin");

module.exports = {
  name: "webview",
  mode: "development",
  entry: {
    goals: path.resolve(__dirname, "html_views/src/goals/goals.ts"),
    ltacprof: path.resolve(__dirname, "html_views/src/ltacprof/ltacprof.ts")
  },
  module: {
    rules: [
      {
        test: /\.ts/,
        use: "ts-loader",
        exclude: /node_modules/
      }
    ]
  },
  resolve: {
    extensions: [".ts", ".js"]
  },
  output: {
    path: path.resolve(__dirname, "out/html_views")
  },
  plugins: [
    new webpack.ProvidePlugin({
      jQuery: "jquery",
      $: "jquery",
      jquery: "jquery"
    }),
    new CopyPlugin([
      {
        from: "html_views/src/**/*.html",
        to: path.resolve(__dirname, "out", "html_views"),
        flatten: true
      },
      {
        from: "html_views/src/**/*.css",
        to: path.resolve(__dirname, "out", "html_views"),
        flatten: true
      },
      {
        from: "client/images/*.svg",
        to: path.resolve(__dirname, "out", "images"),
        flatten: true
      }
    ])
  ]
};
