import * as http from 'http'
import * as url from 'url'
import * as fs from 'fs'
import * as path from 'path'
import * as vscode from 'vscode'
import * as glob from 'glob'
import * as nasync from './nodejs-async'

interface HostedFile {
  fsPath: string,
  contentType?: string,
}

interface Address {
  host: string,
  port: number,
}

const hostedFiles = new Map<string,HostedFile>()
let server : http.Server = null;
let serverReady : Promise<Address> = null;


async function handleRequest(request: http.IncomingMessage, response: http.ServerResponse) {
  const requestPath = url.parse(request.url).pathname;
  const file = hostedFiles.get(requestPath);
  try {
    if(!file || !await nasync.fs.exists(file.fsPath)) {
      respondFileNotFound(response);
      return;
    }
  } catch(err) {
    respondError(response, err);
  }  

  try {
    if(file.contentType)
      response.writeHead(200, {"Content-Type": file.contentType});
    else
      response.writeHead(200, {"Content-Type": "text/html; charset=utf-8"});

    fs.createReadStream(file.fsPath).pipe(response);
  } catch(err) {
    response.end();
  }  
}

function respondError(response: http.ServerResponse, err: any) {
  response.writeHead(500, {"Content-Type": "text/plain"});
  response.write("Error:\n");
  response.write(err.toString() + "\n");
  response.end();
}

function respondFileNotFound(response: http.ServerResponse) {
  response.writeHead(404, {"Content-Type": "text/plain"});
  response.write("404 Not Found\n");
  response.end();
}

export async function serveDirectory(rootPath: string, basePath: string, globPattern: string) : Promise<vscode.Uri|null> {
  if(!rootPath.startsWith('/'))
    rootPath = '/' + rootPath;

  const matches = await new Promise<string[]>((resolve,reject) => glob(globPattern, {cwd: basePath, root: basePath, silent:true, nonull: false}, function(err,matches) {
    if(err)
      reject(err);
    resolve(matches);
  }));

  if(!matches)
    return null;

  matches.forEach(file => {
    hostedFiles.set(path.join(rootPath,file).replace(/\\/g, '/'), {fsPath: path.join(basePath,file)});
  })

  const address = await initServer();
  if(!address)
    return null;
  return vscode.Uri.parse(`http://${address.host}:${address.port}${rootPath}`);
}


export async function serveFile(path: string, file: string, contentType?: string) : Promise<vscode.Uri|null> {
  if(!path.startsWith('/'))
    path = '/' + path;
  hostedFiles.set(path, {fsPath: file, contentType: contentType});
  const address = await initServer();
  if(!address)
    return null;
  return vscode.Uri.parse(`http://${address.host}:${address.port}/${path}`);
}


async function initServer() : Promise<Address> {
  if(!server) { 
    server = http.createServer(handleRequest);
    serverReady = new Promise<Address>((resolve,reject) => {
      try {
        server.listen({port: 0, host: "localhost"}, () => {
          const addr = server.address();
          resolve({host: "localhost", port: addr.port});
        })
        server.on('close', () => {
          server = null;
          serverReady = null;
        })
      } catch(err) {
        reject(err);
      }
    });
    // kill the server when this application closes (don't keep alive)
    server.unref();
  }
  return serverReady;
}
