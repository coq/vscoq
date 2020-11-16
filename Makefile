world: compile
	node_modules/.bin/vsce package

clean:
	rm -rf node_modules out

node_modules:
	npm install

compile: node_modules
	npm run compile
