world: compile
	yarn vsce package

clean:
	rm -rf node_modules out

node_modules:
	yarn install

compile: node_modules
	yarn run compile
