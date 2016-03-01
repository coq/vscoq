'use strict';

export class CancellationSignal {
  private doCancel : ()=>void;
  private cancelled = false;
  public event = new Promise<void>((resolve) => {this.doCancel = resolve});
  
  public cancel() {
    if(this.cancelled)
      return;
    this.cancelled = true;
    this.doCancel();
  }
  
  public isCancelled() {return this.cancelled; }
};

export async function asyncWithTimeout<T>(operation: Thenable<T>, ms: number) : Promise<T> {
  return await Promise.race<T>(
    [ operation
    , new Promise<T>((resolve,reject) => setTimeout(() => reject('timeout'),ms))
    ]);
}

  // export async function asyncOrCancel<T,U>(operation: Thenable<T>, cancel?: Thenable<U>) : Promise<T> {
  //   if(cancel)
  //     return await Promise.race<T>(
  //       [ operation
  //       , cancel.then(() => Promise.reject<T>('operation cancelled'))
  //       ]);
  //   else
  //     return await operation;
  // }
