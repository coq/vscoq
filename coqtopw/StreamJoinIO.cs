using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace coqtopw
{
  public class StreamJoinIO : Stream
  {
    public Stream WriteStream { get; private set; }
    public Stream ReadStream { get; private set; }
    public bool leaveOpen = false;

    public StreamJoinIO(Stream from, Stream to, bool leaveOpen=false)
    {
      WriteStream = to;
      ReadStream = from;
      this.leaveOpen = leaveOpen;
    }

    public override bool CanRead
    {
      get { return ReadStream.CanRead; }
    }

    public override bool CanSeek
    {
      get { return false; }
    }

    public override bool CanWrite
    {
      get { return WriteStream.CanWrite; }
    }

    public override void Flush()
    {
      WriteStream.Flush();
    }

    public override long Length
    {
      get { throw new NotImplementedException(); }
    }

    public override long Position
    {
      get
      {
        throw new NotImplementedException();
      }
      set
      {
        throw new NotImplementedException();
      }
    }

    public override int Read(byte[] buffer, int offset, int count)
    {
      return ReadStream.Read(buffer, offset, count);
    }

    public override long Seek(long offset, SeekOrigin origin)
    {
      throw new NotImplementedException();
    }

    public override void SetLength(long value)
    {
      throw new NotImplementedException();
    }

    public override void Write(byte[] buffer, int offset, int count)
    {
      WriteStream.Write(buffer, offset, count);
    }

    public override void Close()
    {
      if (!leaveOpen)
        try
        {
          WriteStream.Close();
        }
        finally
        {
          ReadStream.Close();
        }
    }

    public override IAsyncResult BeginRead(byte[] buffer, int offset, int count, AsyncCallback callback, object state)
    {
      return ReadStream.BeginRead(buffer, offset, count, callback, state);
    }
    public override int EndRead(IAsyncResult asyncResult)
    {
      return ReadStream.EndRead(asyncResult);
    }

    public override IAsyncResult BeginWrite(byte[] buffer, int offset, int count, AsyncCallback callback, object state)
    {
      return WriteStream.BeginWrite(buffer, offset, count, callback, state);
    }
    public override void EndWrite(IAsyncResult asyncResult)
    {
      WriteStream.EndWrite(asyncResult);
    }

    public override int ReadByte()
    {
      return ReadStream.ReadByte();
    }
    public override void WriteByte(byte value)
    {
      ReadStream.WriteByte(value);
    }

    public override int ReadTimeout
    {
      get
      {
        return ReadStream.ReadTimeout;
      }
      set
      {
        ReadStream.ReadTimeout = value;
      }
    }

    public override int WriteTimeout
    {
      get
      {
        return WriteStream.WriteTimeout;
      }
      set
      {
        WriteStream.WriteTimeout = value;
      }
    }

    public override bool CanTimeout
    {
      get
      {
        return ReadStream.CanTimeout || WriteStream.CanTimeout;
      }
    }

    public override int GetHashCode()
    {
      return ReadStream.GetHashCode() ^ WriteStream.GetHashCode();
    }

    protected override void Dispose(bool disposing)
    {
      if (disposing && !leaveOpen)
      {
        try
        {
          ReadStream.Dispose();
        }
        finally
        {
          WriteStream.Dispose();
        }
      }
    }

    public override string ToString()
    {
      return "Read: " + ReadStream.ToString() + ", Write: " + WriteStream.ToString();
    }

    public override System.Threading.Tasks.Task<int> ReadAsync(byte[] buffer, int offset, int count, System.Threading.CancellationToken cancellationToken)
    {
      return ReadStream.ReadAsync(buffer, offset, count, cancellationToken);
    }

    public override System.Threading.Tasks.Task WriteAsync(byte[] buffer, int offset, int count, System.Threading.CancellationToken cancellationToken)
    {
      return WriteStream.WriteAsync(buffer, offset, count, cancellationToken);
    }

    public override System.Threading.Tasks.Task CopyToAsync(Stream destination, int bufferSize, System.Threading.CancellationToken cancellationToken)
    {
      return ReadStream.CopyToAsync(destination, bufferSize, cancellationToken);
    }

    public override System.Threading.Tasks.Task FlushAsync(System.Threading.CancellationToken cancellationToken)
    {
      return System.Threading.Tasks.Task.WhenAll(ReadStream.FlushAsync(cancellationToken), WriteStream.FlushAsync(cancellationToken));
    }



  }
}
