default: compile

clean:
	rm -rf html_views/node_modules server/node_modules client/node_modules
	rm -rf client/server client/html_views
	rm -rf html_views/jquery

html_views/node_modules:
	cd html_views && npm install

server/node_modules:
	cd server && npm install

client/node_modules:
	cd client && npm install

node_modules: html_views/node_modules server/node_modules client/node_modules

html_views/jquery:
	mkdir -p html_views/jquery
	wget https://code.jquery.com/jquery-2.2.4.min.js -O html_views/jquery/jquery-2.2.4.min.js
	wget https://jqueryui.com/resources/download/jquery-ui-1.12.1.zip
	unzip -p jquery-ui-1.12.1.zip jquery-ui-1.12.1/jquery-ui.min.js > html_views/jquery/jquery-ui.min.js
	rm jquery-ui-1.12.1.zip

compile: node_modules html_views/jquery
	cd server && npm run compile
	cd html_views && npm run compile
	cd client && npm run compile

vsix: clean node_modules
	cd client && vsce package


deps:
	npm install --global vsce


all: vsix
