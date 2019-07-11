using System.Runtime.InteropServices;

class win32 {
  //import in the declaration for GenerateConsoleCtrlEvent
  [DllImport("kernel32.dll", SetLastError=true)]  
  public static extern bool GenerateConsoleCtrlEvent(ConsoleCtrlEvent sigevent, int dwProcessGroupId);

  //[DllImport("kernel32.dll", SetLastError = true)]
  //internal static extern bool AttachConsole(uint dwProcessId);
  //[DllImport("kernel32.dll", SetLastError = true, ExactSpelling = true)]
  //internal static extern bool FreeConsole();
  
  
  //[DllImport("kernel32.dll")]
  //static extern bool SetConsoleCtrlHandler(ConsoleCtrlDelegate HandlerRoutine, bool Add);

  //// Delegate type to be used as the Handler Routine for SCCH
  //delegate Boolean ConsoleCtrlDelegate(uint CtrlType);


  public enum ConsoleCtrlEvent
  {
    CTRL_C = 0,
    CTRL_BREAK = 1,
    CTRL_CLOSE = 2,
    CTRL_LOGOFF = 5,
    CTRL_SHUTDOWN = 6
  }
}

public class Signals
{

  public static void SendCtrlBreak(int clientPid)
  {
    //bool attached = win32.AttachConsole((uint)clientPid);
    bool result = win32.GenerateConsoleCtrlEvent(win32.ConsoleCtrlEvent.CTRL_BREAK, 0);
    //bool result = win32.GenerateConsoleCtrlEvent(win32.ConsoleCtrlEvent.CTRL_C, clientPid);
    //if (attached)
    //  result = win32.FreeConsole();
    //var a = result;
  }
}

