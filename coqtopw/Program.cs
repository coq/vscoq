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
    

    static async Task<Stream> openChannelSocket(string channel) {
      try
      {
        if (channel == "stdfs")
          return new StreamJoinIO(Console.OpenStandardInput(), Console.OpenStandardOutput(), true);
        else
        {
          var match = channelParser.Match(channel);
          var hostname = match.Groups["hostname"].Value;
          var port = int.Parse(match.Groups["port"].Value);
          var socket = new TcpClient();
          await socket.ConnectAsync(hostname, port);
          return socket.GetStream();
        }
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
        var context = new XmlParserContext(null, new XmlNamespaceManager(new NameTable()), null, XmlSpace.None, Encoding.UTF8);

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
          else if(reader.NodeType == XmlNodeType.Element)
          {
            using (var y = reader.ReadSubtree())
            {
              y.Read();
              await writer.WriteAsync(await y.ReadOuterXmlAsync());
              await writer.FlushAsync();
            }
          }
          else
            throw new Exception("XML parsing error.");
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

    static async Task runCoqtop(string coqtopBin, string mainChannel, string controlChannel, bool ideSlave, IEnumerable<string> args)
    {
      var remoteMain = await openChannelSocket(mainChannel);
      var remoteControl = await openChannelSocket(controlChannel);
      Stream localMain;
      Stream localControl;
      var coqtop = new Process();
      coqtop.StartInfo.UseShellExecute = false;
      coqtop.StartInfo.RedirectStandardError = false;
      coqtop.StartInfo.RedirectStandardInput = true;
      coqtop.StartInfo.RedirectStandardOutput = false;
      if (System.Environment.OSVersion.Platform == PlatformID.Win32NT)
      {
        var localMainR = new TcpListener(IPAddress.Loopback, 0);
        var localMainW = new TcpListener(IPAddress.Loopback, 0);
        var localControlR = new TcpListener(IPAddress.Loopback, 0);
        var localControlW = new TcpListener(IPAddress.Loopback, 0);
        localMainR.Start(1);
        localMainW.Start(1);
        localControlR.Start(1);
        localControlW.Start(1);
        var localMainAddr = ((IPEndPoint)localMainR.LocalEndpoint).Address.ToString() + ":" + ((IPEndPoint)localMainR.LocalEndpoint).Port + ":" + ((IPEndPoint)localMainW.LocalEndpoint).Port;
        var localControlAddr = ((IPEndPoint)localControlR.LocalEndpoint).Address.ToString() + ":" + ((IPEndPoint)localControlR.LocalEndpoint).Port + ":" + ((IPEndPoint)localControlW.LocalEndpoint).Port;
        var arguments = String.Format("{0} -main-channel {1} -control-channel {2} ", ideSlave ? "-ideslave" : "", localMainAddr, localControlAddr)
          + String.Join(" ", args);

        coqtop.StartInfo.FileName = coqtopBin;
        coqtop.StartInfo.Arguments = arguments;
        coqtop.Start();
        //var stderr = Console.OpenStandardError();
        //coqtop.StandardError.BaseStream.CopyToAsync(stderr);
        //coqtop.StandardOutput.BaseStream.CopyToAsync(stderr);

        var connections = await Task.WhenAny(new Task<Tuple<Stream,Stream>>[]
          { AcceptCoqTopConnections(localMainR, localMainW, localControlR, localControlW)
          , Task.Run<Tuple<Stream,Stream>>(() => {System.Threading.Thread.Sleep(5000); return (Tuple<Stream,Stream>)null; })
          }).Result;
        if (connections == null)
        {
          await Console.Error.WriteLineAsync("No response from coqtop.");
          System.Environment.Exit(-1);
        }

        localMain = connections.Item1;
        localControl = connections.Item2;

        localMainR.Stop();
        localMainW.Stop();
        localControlR.Stop();
        localControlW.Stop();
      } else {
        var localMainRW = new TcpListener(IPAddress.Loopback, 0);
        var localControlRW = new TcpListener(IPAddress.Loopback, 0);
        var localMainAddr = ((IPEndPoint)localMainRW.LocalEndpoint).Address.ToString() + ":" + ((IPEndPoint)localMainRW.LocalEndpoint).Port;
        var localControlAddr = ((IPEndPoint)localControlRW.LocalEndpoint).Address.ToString() + ":" + ((IPEndPoint)localControlRW.LocalEndpoint).Port;
        var arguments = String.Format("{0} -main-channel {1} -control-channel {2}", ideSlave ? "-ideslave" : "", localMainAddr, localControlAddr)
          + String.Join(" ", args);
        localMainRW.Start();
        localControlRW.Start();

        coqtop = Process.Start(coqtopBin, arguments);

        var localMainConnection = await localMainRW.AcceptTcpClientAsync();
        var localControlConnection = await localControlRW.AcceptTcpClientAsync();
        localMain = localMainConnection.GetStream();
        localControl = localControlConnection.GetStream();
        localMainRW.Stop();
        localControlRW.Stop();
      }


        if (!ideSlave)
          await Task.WhenAny(new Task[]
          { localMain.CopyToAsync(remoteMain)
          , remoteMain.CopyToAsync(localMain)
          , localControl.CopyToAsync(remoteControl)
          , remoteControl.CopyToAsync(localControl)
          });
        else
          await Task.WhenAny(new Task[]
          { localMain.CopyToAsync(remoteMain)
          , copyStreamWithInterrupt(coqtop, remoteMain, localMain)
          , localControl.CopyToAsync(remoteControl)
          , remoteControl.CopyToAsync(localControl)
          });
    }

    // C:/Users/cj/Research/vscoq/coqtopw/bin/Debug/coqtopw.exe -coqtopbin C:/Coq8.5rc1/bin//coqtop -main-channel 127.0.0.1:7806 -control-channel 127.0.0.1:7809 -ideslave -async-proofs on
    static void Main(string[] args)
    {
      //Console.ReadLine();

      Console.CancelKeyPress += new ConsoleCancelEventHandler(Console_CancelKeyPress);

      var coqtopArgs = new List<string>();
      string coqtopBin = null;
      string mainChannel = null;
      string controlChannel = null;
      bool ideSlave = false;

      for (int idx = 0; idx < args.Length; ++idx)
      {
        if (args[idx] == "-coqtopbin")
          coqtopBin = args[++idx];
        else if (args[idx] == "-main-channel")
          mainChannel = args[++idx];
        else if (args[idx] == "-control-channel")
          controlChannel = args[++idx];
        else if (args[idx] == "-ideslave")
          ideSlave = true;
        else
          coqtopArgs.Add(args[idx]);
      }

      if (coqtopBin != null && mainChannel != null && controlChannel != null) {
        try
        {
          Task.WaitAll(runCoqtop(coqtopBin, mainChannel, controlChannel, ideSlave, coqtopArgs));
        }
        catch (Exception error)
        {
          Console.Error.WriteLine("Error communicating with coqtop.");
          Console.Error.WriteLine("Reason: " + error.ToString());
          System.Environment.Exit(-1);
        }
      } else
        System.Console.Error.WriteLine(
          "Usage: coqtopw" +
          " -coqtopbin <path-to-coqtop-binary>" +
          " -main-channel <\"stdfds\"|hostname:port>" +
          " -control-channel <hostname:port> [coqtop options...]");
    }
  }
}
