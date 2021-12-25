world: node_modules
	node_modules/.bin/vsce package

clean:
	rm -rf node_modules client/out server/out html_views/out

node_modules: package.json
	npm install

compile: node_modules
	npm run compile
