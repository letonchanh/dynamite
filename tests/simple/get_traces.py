#!/usr/bin/python

import lldb
import os
import sage.all

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
print "Creating a target for {}".format(exe)

# target = debugger.CreateTargetWithFileAndArch (exe, lldb.LLDB_ARCH_DEFAULT)
target = debugger.CreateTarget (exe)

if target:
    # If the target is valid set a breakpoint at main
    exe = target.GetExecutable().GetFilename()
    main_bp = target.BreakpointCreateByName ("main", exe)
    vtrace_bps = target.BreakpointCreateByRegex("vtrace*", exe)

    print main_bp
    print vtrace_bps
    for vtrace_bp in vtrace_bps:
        vtrace_func = vtrace_bp.GetAddress().GetFunction()
        print vtrace_func.GetName()
        func_type = vtrace_func.GetType()
        assert(func_type.IsFunctionType())
        arg_types = func_type.GetFunctionArgumentTypes()
        for i in range(0, arg_types.GetSize()):
            print "{}: {}".format(vtrace_func.GetArgumentName(i), arg_types.GetTypeAtIndex(i))

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
            cnt = 0
            bnd = 100
            while thread.GetStopReason() == lldb.eStopReasonBreakpoint and cnt < bnd:
                frame = thread.GetFrameAtIndex(0)
                # Print some simple frame info
                print frame
                if frame:
                    function = frame.GetFunction()
                    print function
                    if function.GetName() == 'vtrace2':
                        cnt = cnt + 1
                    vars = frame.GetVariables(True, True, True, True)
                    for v in vars:
                        print("{}: {}".format(v.GetName(), v.GetValue()))
                process.Continue()