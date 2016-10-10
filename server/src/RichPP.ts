import * as xml2js from 'xml2js';

interface RichPP {

}

interface RichPPObject {
  _: string,
}


export function richppToMarkdown(text: string) : Promise<string> {
  return new Promise<string>((resolve,reject) => {
    const xml = xml2js.parseString(text, {
      charkey: '_char',
      trim: false,
      explicitArray: false,     
    }, (err:any,result:any) => {
      if(err || !result || result.hasOwnProperty('richpp'))
        resolve(text);
      else
        resolve((<RichPPObject>result['richpp'])._);
    });
  })
}