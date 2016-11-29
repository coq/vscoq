all:
	vsce install --global vsce
	cd server && npm install
	cd html_views && npm install
	cd client && npm install && vsce package
