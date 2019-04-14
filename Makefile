clean:
	rm -rf html_views/node_modules server/node_modules client/node_modules
	rm -rf client/server client/html_views

html_views/node_modules:
	cd html_views && npm install

server/node_modules:
	cd server && npm install

client/node_modules:
	cd client && npm install

node_modules: html_views/node_modules server/node_modules client/node_modules

compile: node_modules
	cd server && npm run compile
	cd html_views && npm run compile
	cd client && npm run compile

vsix: clean node_modules
	cd client && vsce package


deps:
	npm install --global vsce


all: vsix
