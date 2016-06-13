using System;
using NUnit.Framework;
using System.Diagnostics;
using System.Linq;
using System.IO;
using System.Xml;
using System.Text;

namespace UnitTests
{
  class CoqtopXmlReader
  {
    XmlReader reader;
    public CoqtopXmlReader(StreamReader source)
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
      this.reader = XmlTextReader.Create(source, settings, context);
    }

    public string Read()
    {
      Assert.IsTrue(reader.Read());
      var x = reader.ReadSubtree();
      x.Read();
      return x.ReadOuterXml();
    }
  }


  [TestFixture]
  public class UnitTest1
  {
    static string coqtopBin = "C:/Coq8.5lp/bin/coqtop.exe";
    static string coqtopw = AppDomain.CurrentDomain.SetupInformation.ApplicationBase + "coqtopw.exe";
    //"../../../bin/Debug/coqtopw.exe";

    private static Process runProgram(string bin, string args)
    {
      var coqtop = new Process();
      coqtop.StartInfo.UseShellExecute = false;
      coqtop.StartInfo.RedirectStandardError = true;
      coqtop.StartInfo.RedirectStandardInput = true;
      coqtop.StartInfo.RedirectStandardOutput = true;
      coqtop.StartInfo.FileName = bin;

      coqtop.StartInfo.Arguments = args;
      coqtop.Start();
      return coqtop;
    }


    [Test]
    public void TestBasicCoqTop()
    {
      var p = runProgram(coqtopBin, "");
      p.StandardInput.WriteLine("Quit.");
      p.StandardInput.Flush();
      p.WaitForExit();
      Assert.AreEqual(0, p.ExitCode);
      Assert.IsTrue(p.StandardOutput.ReadLine().StartsWith("Welcome to Coq"));
      Assert.AreEqual(null, p.StandardOutput.ReadLine());
      Assert.AreEqual("", p.StandardError.ReadLine().TrimEnd());
      Assert.AreEqual("Coq <", p.StandardError.ReadLine().TrimEnd());
    }

    [Test]
    public void TestBasicCoqTopPassthrough()
    {
      var p = runProgram(coqtopw, String.Format("-coqtopbin {0}", coqtopBin));
      p.StandardInput.WriteLine("Quit.");
      p.StandardInput.Flush();
      p.WaitForExit();
      Assert.AreEqual(0, p.ExitCode);
      Assert.IsTrue(p.StandardOutput.ReadLine().StartsWith("Welcome to Coq"));
      Assert.AreEqual(null, p.StandardOutput.ReadLine());
      Assert.AreEqual("", p.StandardError.ReadLine().TrimEnd());
      Assert.AreEqual("Coq <", p.StandardError.ReadLine().TrimEnd());
    }

    [Test]
    public void TestIdeslaveStdfds()
    {
      var p = runProgram(coqtopw, String.Format("-coqtopbin {0} -ideslave -main-channel stdfds", coqtopBin));
      var responses = new CoqtopXmlReader(p.StandardOutput);
      
      p.StandardInput.Write("<call val=\"Init\"><option val=\"none\"/></call>");
      var response1 = responses.Read();
      Assert.AreEqual("<value val=\"good\"><state_id val=\"1\" /></value>", response1);

      p.StandardInput.Write("<call val=\"Query\"><pair><string>Check nat.</string><state_id val=\"0\"/></pair></call>");
      var response2 = new String[] { responses.Read(), responses.Read(), responses.Read() };
      Assert.IsTrue(response2.Contains("<feedback object=\"state\" route=\"0\"><state_id val=\"1\" /><feedback_content val=\"processed\" /></feedback>"));
      Assert.IsTrue(response2.Contains("<message><message_level val=\"notice\" /><string>nat\n     : Set</string></message>"));
      Assert.IsTrue(response2.Contains("<value val=\"good\"><string></string></value>"));

      p.StandardInput.WriteLine("<call val=\"Quit\"><unit/></call>");
      var response3 = responses.Read();
      Assert.AreEqual("<value val=\"good\"><unit /></value>", response3);

      p.StandardInput.Flush();
      p.WaitForExit();
      Assert.AreEqual(0, p.ExitCode);
    }
  }
}
