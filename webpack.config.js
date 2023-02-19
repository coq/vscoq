//@ts-check

'use strict';

const client = require('./webpack.client.config.js');
const html_views = require('./webpack.html_views.config.js');
const server = require('./webpack.server.config.js');


module.exports = [client,html_views,server];