using System;
using System.Collections.Generic;
using System.Text;
using System.IO;
using System.Linq;

namespace coqtopw
{
  public class TraceStream : Stream
  {
    public Stream ObservedStream { get; private set; }
    public bool leaveOpen = false;
    private Stream trace;
    private byte[] tracePrefix;
    private byte[] traceTempPostfix;

    /**
     * @param tracePostfix -- bytes to write after each log message; NOTE: the postfix will always be overwritten by subsequent messages; it is intended to maintain proper XML structure
     */
    public TraceStream(Stream observed, byte[] tracePrefix, byte[] traceTempPostfix, Stream trace, bool leaveOpen = false)
    {
      ObservedStream = observed;
      this.trace = trace;
      this.tracePrefix = tracePrefix;
      this.traceTempPostfix = traceTempPostfix;
      this.leaveOpen = leaveOpen;
    }

    public override bool CanRead
    {
      get { return ObservedStream.CanRead; }
    }

    public override bool CanSeek
    {
      get { return ObservedStream.CanSeek; }
    }

    public override bool CanWrite
    {
      get { return ObservedStream.CanWrite; }
    }

    public override void Flush()
    {
      ObservedStream.Flush();
    }

    public override long Length
    {
      get { return ObservedStream.Length; }
    }

    public override long Position
    {
      get
      {
        return ObservedStream.Position;
      }
      set
      {
        ObservedStream.Position = value;
      }
    }

    public override int Read(byte[] buffer, int offset, int count)
    {
      return ObservedStream.Read(buffer, offset, count);
    }

    public override long Seek(long offset, SeekOrigin origin)
    {
      return ObservedStream.Seek(offset,origin);
    }

    public override void SetLength(long value)
    {
      ObservedStream.SetLength(value);
    }

    private void WriteTrace(byte[] buffer, int offset, int count)
    {
      var b = tracePrefix.Concat(buffer.Skip(offset).Take(count)).Concat(this.traceTempPostfix).ToArray();
      trace.Write(b, 0, b.Length);
      trace.Position = trace.Position - this.traceTempPostfix.Length;
      trace.Flush();
    }


    public override void Write(byte[] buffer, int offset, int count)
    {
      WriteTrace(buffer, offset, count);
      ObservedStream.Write(buffer, offset, count);
    }

    public override void Close()
    {
      if (!leaveOpen)
        try
        {
          ObservedStream.Close();
        }
        finally
        {
        }
    }

    public override IAsyncResult BeginRead(byte[] buffer, int offset, int count, AsyncCallback callback, object state)
    {
      return ObservedStream.BeginRead(buffer, offset, count, callback, state);
    }
    public override int EndRead(IAsyncResult asyncResult)
    {
      return ObservedStream.EndRead(asyncResult);
    }


    public override IAsyncResult BeginWrite(byte[] buffer, int offset, int count, AsyncCallback callback, object state)
    {
      WriteTrace(buffer, offset, count);
      return ObservedStream.BeginWrite(buffer, offset, count, callback, state);
    }
    public override void EndWrite(IAsyncResult asyncResult)
    {
      ObservedStream.EndWrite(asyncResult);
    }

    public override int ReadByte()
    {
      return ObservedStream.ReadByte();
    }
    public override void WriteByte(byte value)
    {
      WriteTrace(new byte[]{value}, 0, 1);
      ObservedStream.WriteByte(value);
    }

    public override int ReadTimeout
    {
      get
      {
        return ObservedStream.ReadTimeout;
      }
      set
      {
        ObservedStream.ReadTimeout = value;
      }
    }

    public override int WriteTimeout
    {
      get
      {
        return ObservedStream.WriteTimeout;
      }
      set
      {
        ObservedStream.WriteTimeout = value;
      }
    }

    public override bool CanTimeout
    {
      get
      {
        return ObservedStream.CanTimeout;
      }
    }

    public override int GetHashCode()
    {
      return ObservedStream.GetHashCode();
    }

    protected override void Dispose(bool disposing)
    {
      if (disposing && !leaveOpen)
      {
        try
        {
          ObservedStream.Dispose();
        }
        finally
        {
        }
      }
    }

    public override string ToString()
    {
      return ObservedStream.ToString();
    }

    public override System.Threading.Tasks.Task<int> ReadAsync(byte[] buffer, int offset, int count, System.Threading.CancellationToken cancellationToken)
    {
      return ObservedStream.ReadAsync(buffer, offset, count, cancellationToken);
    }

    public override System.Threading.Tasks.Task WriteAsync(byte[] buffer, int offset, int count, System.Threading.CancellationToken cancellationToken)
    {
      WriteTrace(buffer, offset, count);
      return ObservedStream.WriteAsync(buffer, offset, count, cancellationToken);
    }

    public override System.Threading.Tasks.Task CopyToAsync(Stream destination, int bufferSize, System.Threading.CancellationToken cancellationToken)
    {
      return ObservedStream.CopyToAsync(destination, bufferSize, cancellationToken);
    }

    public override System.Threading.Tasks.Task FlushAsync(System.Threading.CancellationToken cancellationToken)
    {
      return ObservedStream.FlushAsync(cancellationToken);
    }



  }
}
