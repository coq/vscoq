using System;
using System.Collections.Generic;
using System.Text;
using System.Threading.Tasks;
using System.Net.Sockets;
using System.Net;
using System.Text.RegularExpressions;
using System.IO;
using System.Xml;
using Process = System.Diagnostics.Process;

namespace coqtopw
{
  class Program
  {

    //set up the parents CtrlC event handler, so we can ignore the event while sending to the child
    public static volatile bool SENDING_CTRL_C_TO_CHILD = false;
    static void Console_CancelKeyPress(object sender, ConsoleCancelEventArgs e)
    {
      e.Cancel = true;
    }

    static Regex channelParser = new Regex("^(?<hostname>[^:].*):(?<port>[0-9]*)$");
    static Regex channelParser2 = new Regex("^(?<hostname>[^:].*):(?<portR>[0-9]*):(?<portW>[0-9]*)$");
    

    static async Task<Stream> openChannelSocket(string channel) {
      try
      {
        if(channel == null)
          return Stream.Null;
        else if (channel == "stdfds")
          return new StreamJoinIO(Console.OpenStandardInput(), Console.OpenStandardOutput(), true);
        else if (channelParser2.IsMatch(channel))
        {
          var match = channelParser2.Match(channel);
          var hostname = match.Groups["hostname"].Value;
          var portR = int.Parse(match.Groups["portR"].Value);
          var portW = int.Parse(match.Groups["portW"].Value);
          var socketR = new TcpClient();
          var socketW = new TcpClient();
          await socketR.ConnectAsync(hostname, portR);
          await socketW.ConnectAsync(hostname, portW);
          return new StreamJoinIO(socketW.GetStream(), socketR.GetStream());
        }
        else if (channelParser.IsMatch(channel))
        {
          var match = channelParser.Match(channel);
          var hostname = match.Groups["hostname"].Value;
          var port = int.Parse(match.Groups["port"].Value);
          var socket = new TcpClient();
          await socket.ConnectAsync(hostname, port);
          return socket.GetStream();
        }
        else
          throw new Exception("Invalid channel syntax");
      }
      catch (Exception err)
      {
        Console.Error.WriteLine("Could not connect to " + channel);
        Console.Error.WriteLine("Reason: " + err.ToString());
        System.Environment.Exit(-1);
        return null;
      }
    }

    static async Task copyStreamWithInterrupt(Process coqtop, Stream from, Stream to)
    {
      try
      {
        var settings = new XmlReaderSettings();
        settings.Async = true;
        settings.CheckCharacters = false;
        settings.ValidationType = ValidationType.None;
        settings.ConformanceLevel = ConformanceLevel.Fragment;
        settings.DtdProcessing = DtdProcessing.Parse;
        var context = new XmlParserContext(null, new XmlNamespaceManager(new NameTable()), null, XmlSpace.None, Encoding.UTF8);
        context.InternalSubset = "<!ENTITY nbsp \"&#160;\">";
        context.DocTypeName = "coq";

        var reader = XmlTextReader.Create(from, settings, context);
        var writer = new StreamWriter(to);
        while (await reader.ReadAsync())
        {
          if (reader.NodeType == XmlNodeType.Element && reader.Depth == 0 && reader.Name == "call" && reader.GetAttribute("val") == "Interrupt")
          {
            await Console.Error.WriteLineAsync("Sending ctrl+break");
            Signals.SendCtrlBreak(coqtop.Id);
            using (var y = reader.ReadSubtree())
            {
              y.Read();
              await y.ReadOuterXmlAsync();
            }
            //await reader.SkipAsync();
          }
          else if (reader.NodeType == XmlNodeType.Element)
          {
            using (var y = reader.ReadSubtree())
            {
              y.Read();
              await writer.WriteAsync(await y.ReadOuterXmlAsync());
              await writer.FlushAsync();
            }
          }
        }
      }
      catch (Exception error)
      {
        Console.Error.WriteLine("Error reading main channel write stream.");
        Console.Error.WriteLine("Reason: " + error.ToString());
        System.Environment.Exit(-1);
      }
    }

    static async Task<Tuple<Stream,Stream>> AcceptCoqTopConnections(TcpListener localMainR, TcpListener localMainW, TcpListener localControlR, TcpListener localControlW)
    {
      var localMainRConnection = await localMainR.AcceptTcpClientAsync();
      var localMainWConnection = await localMainW.AcceptTcpClientAsync();
      var localControlRConnection = await localControlR.AcceptTcpClientAsync();
      var localControlWConnection = await localControlW.AcceptTcpClientAsync();
      var localMain = new StreamJoinIO(localMainRConnection.GetStream(), localMainWConnection.GetStream());
      var localControl = new StreamJoinIO(localControlRConnection.GetStream(), localControlWConnection.GetStream());
      return Tuple.Create<Stream,Stream>(localMain, localControl);
    }

    static async Task runCoqtop(string coqtopBin, string mainChannel, string controlChannel, bool ideSlave, IEnumerable<string> args, string traceFile)
    {
      var editorMain = await openChannelSocket(mainChannel);
      var editorControl = await openChannelSocket(controlChannel);
      Stream coqtopMain;
      Stream coqtopControl;
      var coqtop = new Process();
      coqtop.StartInfo.UseShellExecute = false;
      coqtop.StartInfo.RedirectStandardError = false;
      coqtop.StartInfo.RedirectStandardInput = true;
      coqtop.StartInfo.RedirectStandardOutput = false;
      //if (System.Environment.OSVersion.Platform == PlatformID.Win32NT)
      //{// coqtop expects a dedicated read and write socket for each channel on Windows due to a bug in OCaml
        var coqtopMainR = new TcpListener(IPAddress.Loopback, 0);
        var coqtopMainW = new TcpListener(IPAddress.Loopback, 0);
        var coqtopControlR = new TcpListener(IPAddress.Loopback, 0);
        var coqtopControlW = new TcpListener(IPAddress.Loopback, 0);
        coqtopMainR.Start(1);
        coqtopMainW.Start(1);
        coqtopControlR.Start(1);
        coqtopControlW.Start(1);
        var coqtopMainAddr = ((IPEndPoint)coqtopMainR.LocalEndpoint).Address.ToString() + ":" + ((IPEndPoint)coqtopMainR.LocalEndpoint).Port + ":" + ((IPEndPoint)coqtopMainW.LocalEndpoint).Port;
        var coqtopControlAddr = ((IPEndPoint)coqtopControlR.LocalEndpoint).Address.ToString() + ":" + ((IPEndPoint)coqtopControlR.LocalEndpoint).Port + ":" + ((IPEndPoint)coqtopControlW.LocalEndpoint).Port;
        var arguments = String.Format("{0} -main-channel {1} -control-channel {2} ", ideSlave ? "-ideslave" : "", coqtopMainAddr, coqtopControlAddr)
          + String.Join(" ", args);

        coqtop.StartInfo.FileName = coqtopBin;
        coqtop.StartInfo.Arguments = arguments;
        coqtop.Start();
        //var stderr = Console.OpenStandardError();
        //coqtop.StandardError.BaseStream.CopyToAsync(stderr);
        //coqtop.StandardOutput.BaseStream.CopyToAsync(stderr);

        var connections = await Task.WhenAny(new Task<Tuple<Stream,Stream>>[]
          { AcceptCoqTopConnections(coqtopMainR, coqtopMainW, coqtopControlR, coqtopControlW)
          , Task.Run<Tuple<Stream,Stream>>(() => {System.Threading.Thread.Sleep(5000); return (Tuple<Stream,Stream>)null; })
          }).Result;
        if (connections == null)
        {
          await Console.Error.WriteLineAsync("No response from coqtop.");
          System.Environment.Exit(-1);
        }

        coqtopMain = connections.Item1;
        coqtopControl = connections.Item2;

        coqtopMainR.Stop();
        coqtopMainW.Stop();
        coqtopControlR.Stop();
        coqtopControlW.Stop();
      //} else {
      //  var coqtopMainRW = new TcpListener(IPAddress.Loopback, 0);
      //  var coqtopControlRW = new TcpListener(IPAddress.Loopback, 0);
      //  var coqtopMainAddr = ((IPEndPoint)coqtopMainRW.LocalEndpoint).Address.ToString() + ":" + ((IPEndPoint)coqtopMainRW.LocalEndpoint).Port;
      //  var coqtopControlAddr = ((IPEndPoint)coqtopControlRW.LocalEndpoint).Address.ToString() + ":" + ((IPEndPoint)coqtopControlRW.LocalEndpoint).Port;
      //  var arguments = String.Format("{0} -main-channel {1} -control-channel {2}", ideSlave ? "-ideslave" : "", coqtopMainAddr, coqtopControlAddr)
      //    + String.Join(" ", args);
      //  coqtopMainRW.Start();
      //  coqtopControlRW.Start();

      //  coqtop = Process.Start(coqtopBin, arguments);

      //  var coqtopMainConnection = await coqtopMainRW.AcceptTcpClientAsync();
      //  var coqtopControlConnection = await coqtopControlRW.AcceptTcpClientAsync();
      //  coqtopMain = coqtopMainConnection.GetStream();
      //  coqtopControl = coqtopControlConnection.GetStream();
      //  coqtopMainRW.Stop();
      //  coqtopControlRW.Stop();
      //}

      FileStream trace = null;
      if (traceFile != null)
      {
        try
        {
          File.Delete(traceFile);
          trace = new FileStream(traceFile, FileMode.Create);
        }
        catch (Exception)
        {
          trace = null;
        }
      }

      if (trace != null)
      {
        coqtopMain = new TraceStream(coqtopMain, System.Text.Encoding.UTF8.GetBytes("\n<!-- editor->coqtop main-channel: -->\n"), trace);
        editorMain = new TraceStream(editorMain, System.Text.Encoding.UTF8.GetBytes("\n<!-- coqtop->editor main-channel: -->\n"), trace);
        coqtopControl = new TraceStream(coqtopControl, System.Text.Encoding.UTF8.GetBytes("\n<!-- editor->coqtop control-channel: -->\n"), trace);
        editorControl = new TraceStream(editorControl, System.Text.Encoding.UTF8.GetBytes("\n<!-- coqtop->editor control-channel: -->\n"), trace);
      }

      var tasks = new List<Task>();
      tasks.Add(coqtopMain.CopyToAsync(editorMain));
      if (!ideSlave)
        tasks.Add(editorMain.CopyToAsync(coqtopMain));
      else
        tasks.Add(copyStreamWithInterrupt(coqtop, editorMain, coqtopMain));
      if (controlChannel != null)
      {
        tasks.Add(coqtopControl.CopyToAsync(editorControl));
        tasks.Add(editorControl.CopyToAsync(coqtopControl));
      }

      await Task.WhenAny(tasks);        
    }

   

    // C:/Users/cj/Research/vscoq/coqtopw/bin/Debug/coqtopw.exe -coqtopbin C:/Coq8.5rc1/bin//coqtop -main-channel 127.0.0.1:7806 -control-channel 127.0.0.1:7809 -ideslave -async-proofs on
    static int Main(string[] args)
    {
      //Console.ReadLine();
      //System.Threading.Thread.Sleep(3000);

      Console.CancelKeyPress += new ConsoleCancelEventHandler(Console_CancelKeyPress);
      //while (!System.Diagnostics.Debugger.IsAttached)
      //  ;

      var coqtopArgs = new List<string>();
      string coqtopBin = Environment.GetEnvironmentVariable("COQTOP");
      //if(coqtopBin == null)
      //  coqtopBin = "coqtop_real.exe";
      string mainChannel = null;
      string controlChannel = null;
      bool ideSlave = false;
      string traceFile = Environment.GetEnvironmentVariable("COQTOPTRACE");
      if (traceFile != null && traceFile.Trim() == "")
        traceFile = null;
      //traceFile = @"C:\Users\cj\Desktop\coqtrace.txt";

      for (int idx = 0; idx < args.Length; ++idx)
      {
        if (args[idx] == "-coqtopbin")
          coqtopBin = args[++idx];
        else if (args[idx] == "-tracefile")
          traceFile = args[++idx];
        else if (args[idx] == "-main-channel")
          mainChannel = args[++idx];
        else if (args[idx] == "-control-channel")
          controlChannel = args[++idx];
        else if (args[idx] == "-ideslave")
          ideSlave = true;
        else
          coqtopArgs.Add(args[idx]);
      }

      if (coqtopBin != null && Path.GetFullPath(System.Diagnostics.Process.GetCurrentProcess().ProcessName) == Path.GetFullPath(coqtopBin))
      {
        Console.Error.WriteLine("Coqtop bin: " + coqtopBin + " points to me (do you want to fork bomb?)");
      }

      if (coqtopBin != null && ideSlave && mainChannel!=null)
      {
        try
        {
          Task.WaitAll(runCoqtop(coqtopBin, mainChannel, controlChannel, ideSlave, coqtopArgs, traceFile));
          return 0;
        }
        catch (Exception error)
        {
          Console.Error.WriteLine("Error communicating with coqtop.");
          Console.Error.WriteLine("Reason: " + error.ToString());
          return -1;
        }
      }
      else if (coqtopBin != null && coqtopBin.Trim() != "")
      {
        var coqtop = new Process();
        coqtop.StartInfo.UseShellExecute = false;
        coqtop.StartInfo.RedirectStandardError = false;
        coqtop.StartInfo.RedirectStandardInput = false;
        coqtop.StartInfo.RedirectStandardOutput = false;
        coqtop.StartInfo.FileName = coqtopBin;

        // Add back the arguments that were captured
        if (mainChannel != null) { coqtopArgs.Add("-main-channel"); coqtopArgs.Add(mainChannel); }
        if (controlChannel != null) { coqtopArgs.Add("-control-channel"); coqtopArgs.Add(controlChannel); }
        if (ideSlave) { coqtopArgs.Add("-ideslave"); }

        coqtop.StartInfo.Arguments = String.Join(" ", coqtopArgs);
        coqtop.Start();
        coqtop.WaitForExit();
        return coqtop.ExitCode;
      }
      else
      {
        System.Console.Error.WriteLine(
          "Usage: coqtopw" +
          " -coqtopbin <path-to-coqtop-binary>" +
          " -main-channel <\"stdfds\"|hostname:port>" +
          " -control-channel <hostname:port> [coqtop options...]");
        return -1;
      }
    }
  }
}
