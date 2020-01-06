#!/usr/bin/python

import lldb
import os

def disassemble_instructions(insts):
    for i in insts:
        print i

# Set the path to the executable to debug
exe = "./a.out"

# Create a new debugger instance
debugger = lldb.SBDebugger.Create()

# When we step or continue, don't return from the function until the process
# stops. Otherwise we would have to handle the process events ourselves which, while doable is
#a little tricky.  We do this by setting the async mode to false.
debugger.SetAsync (False)

# Create a target from a file and arch
print "Creating a target for '%s'" % exe

# target = debugger.CreateTargetWithFileAndArch (exe, lldb.LLDB_ARCH_DEFAULT)
target = debugger.CreateTarget (exe)

if target:
    # If the target is valid set a breakpoint at main
    exe = target.GetExecutable().GetFilename()
    main_bp = target.BreakpointCreateByName ("main", exe)
    vtrace_bps = target.BreakpointCreateByRegex("vtrace*", exe)

    print main_bp
    print vtrace_bps

    # Launch the process. Since we specified synchronous mode, we won't return
    # from this function until we hit the breakpoint at main
    process = target.LaunchSimple (None, None, os.getcwd())
    # Print some simple process info
    print process

    # Make sure the launch went ok
    if process:
        state = process.GetState ()
        opt = lldb.SBExpressionOptions()
        opt.SetIgnoreBreakpoints(False)
        v = target.EvaluateExpression('mainQ(1, 2)', opt)

        thread = process.GetThreadAtIndex (0)
        # Print some simple thread info
        print thread
        if thread:
            while thread.GetStopReason() == lldb.eStopReasonBreakpoint:
                frame = thread.GetFrameAtIndex(0)
                # Print some simple frame info
                print frame
                if frame:
                    function = frame.GetFunction()
                    print function
                process.Continue()