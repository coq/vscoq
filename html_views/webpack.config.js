//@ts-check

const path = require('path');
const webpack = require('webpack');

function getWebviewConfig(env) {
	/** @type webpack.Configuration */
	let webview = {
		name: 'webview',
		mode: env.production ? 'production' : 'development',
		entry: {
			goals: './src/goals/goals.ts',
			ltacprof: './src/ltacprof/ltacprof.ts'
		},
		module: {
			rules: [
				{
					test: /\.ts/,
					use: 'ts-loader',
					exclude: /node_modules/
				},
				{
					test: /\.css/,
					use: ['style-loader', 'css-loader']
				}
			]
		},
		resolve: {
			extensions: ['.ts', '.js']
		},
		output: {
			filename: '[name]/[name].js',
			path: path.resolve(__dirname, '../client/html_views')
		},
		plugins: [
			new webpack.ProvidePlugin({
			  jQuery: 'jquery',
			  $: 'jquery',
			  jquery: 'jquery'
			})
		  ]
	};

	return webview;
}

module.exports =  function(env) {
	env = env || {};
	env.production = !!env.production;
	return [getWebviewConfig(env)];
};
