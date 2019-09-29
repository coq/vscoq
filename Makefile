world: compile
	cd client && node_modules/.bin/vsce package

clean:
	rm -rf node_modules html_views/node_modules server/node_modules client/node_modules
	rm -rf client/server client/html_views

node_modules:
	npm install

compile: node_modules
	npm run compile
