import lldb
import os

from utils import settings
import settings as dig_settings
import helpers.vcommon as dig_common_helpers
from data.prog import Symb, Symbs, DSymbs, Prog
from data.traces import Inp, Inps, DTraces

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

def create_lldb_target(exe):
    # Create a new debugger instance
    debugger = lldb.SBDebugger.Create()

    # When we step or continue, don't return from the function until the process
    # stops. Otherwise we would have to handle the process events ourselves which, while doable is
    #a little tricky.  We do this by setting the async mode to false.
    debugger.SetAsync (False)

    # Create a target from a file and arch
    mlog.debug("Creating a target for {}".format(exe))

    # target = debugger.CreateTargetWithFileAndArch (exe, lldb.LLDB_ARCH_DEFAULT)
    target = debugger.CreateTarget(exe)
    assert target, target
    return target

class Bin(Prog):
    def __init__(self, inloop_loc, exe):
        assert os.path.isfile(exe), exe
        self.target = create_lldb_target(exe)

        self.inp_decls = DSymbs([])
        self.inv_decls = DSymbs([])
        self.mainQ_name = ""
        self.inloop_loc = inloop_loc
        self._cache = {}  # inp -> traces (str)

    def parse(self):
        target = self.target
        exe = target.GetExecutable().GetFilename()
        main_bp = target.BreakpointCreateByName("main", exe)
        vassume_bp = target.BreakpointCreateByName(dig_settings.ASSUME_INDICATOR, exe)
        vtrace_bps = target.BreakpointCreateByRegex("^" + dig_settings.TRACE_INDICATOR, exe)
        mainQ_bps = target.BreakpointCreateByRegex("^" + dig_settings.MAINQ_FUN, exe)

        mlog.debug("main_bp: {}".format(main_bp))
        mlog.debug("vassume_bp: {}".format(vassume_bp))
        mlog.debug("vtrace_bps: {}".format(vtrace_bps))
        mlog.debug("mainQ_bps: {}".format(mainQ_bps))

        def parse_bp(bp):
            func = bp.GetAddress().GetFunction()
            func_name = func.GetName()
            func_type = func.GetType()
            mlog.debug("{}: {}".format(func_name, func_type))
            assert func_type.IsFunctionType(), func_type
            arg_types = func_type.GetFunctionArgumentTypes()
            arg_sig = []
            for i in range(0, arg_types.GetSize()):
                arg_name = func.GetArgumentName(i)
                arg_type = arg_types.GetTypeAtIndex(i)
                if arg_type == arg_type.GetBasicType(lldb.eBasicTypeInt):
                    arg_type_str = 'I'
                elif arg_type == arg_type.GetBasicType(lldb.eBasicTypeFloat):
                    arg_type_str = 'F'
                elif arg_type == arg_type.GetBasicType(lldb.eBasicTypeDouble):
                    arg_type_str = 'D'
                else:
                    assert False, arg_type
                arg_sig.append(Symb(arg_name, arg_type_str))
            return (func_name, Symbs(arg_sig))

        inv_decls = DSymbs([parse_bp(vtrace_bp) for vtrace_bp in vtrace_bps])
        # mlog.debug("inv_decls: {}".format(inv_decls))

        inp_decls = DSymbs([parse_bp(mainQ_bp) for mainQ_bp in mainQ_bps])
        # mlog.debug("inp_decls: {}".format(inp_decls))
        
        mainQ_name, inp_decls = next(iter(inp_decls.items()))
        # mlog.debug("mainQ_name: {}".format(mainQ_name))

        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self.mainQ_name = mainQ_name

        return (inp_decls, inv_decls, mainQ_name)

    def _get_traces(self, inp):
        # mlog.debug("inp: {}".format(inp))
        target = self.target
        # If the target is valid set a breakpoint at main
        # exe = target.GetExecutable().GetFilename()
        # main_bp = target.BreakpointCreateByName ("main", exe)
        # vtrace_bps = target.BreakpointCreateByRegex("^vtrace", exe)
        # mainQ_bps = target.BreakpointCreateByRegex("^mainQ", exe)

        # Launch the process. Since we specified synchronous mode, we won't return
        # from this function until we hit the breakpoint at main
        process = target.LaunchSimple(None, None, os.getcwd())
        # Print some simple process info
        mlog.debug("process: {}".format(process))

        # Make sure the launch went ok
        assert process, process
        state = process.GetState()
        opt = lldb.SBExpressionOptions()
        opt.SetIgnoreBreakpoints(False)
        inp_d = dict(zip([s.name if isinstance(s, Symb) else s for s in inp.ss], inp.vs))
        # mlog.debug("inp_d: {}".format(inp_d))
        inp_ = ', '.join(map(str, [inp_d[s.name] for s in self.inp_decls]))
        v = target.EvaluateExpression(self.mainQ_name + '(' + inp_ + ')', opt)
        thread = process.GetThreadAtIndex(0)
        # Print some simple thread info
        # mlog.debug("thread: {}".format(thread))
        assert thread, thread
        cnt = 0
        bnd = 500
        traces = []
        while thread.GetStopReason() == lldb.eStopReasonBreakpoint and cnt < bnd:
            frame = thread.GetFrameAtIndex(0)
            # Print some simple frame info
            # mlog.debug("frame: {}".format(frame))
            assert frame, frame
            function = frame.GetFunction()
            # mlog.debug("function: {}".format(function))
            func_name = function.GetName()
            if func_name == dig_settings.ASSUME_INDICATOR:
                assume_cond = frame.GetVariables(True, True, True, True)
                mlog.debug("assume_cond: {}".format(assume_cond))
                assert len(assume_cond) == 1
                if assume_cond[0].GetValue() == '0':
                    break
                else:
                    process.Continue()
            
            if func_name == self.inloop_loc:
                cnt = cnt + 1
            if func_name in self.inv_decls:
                inv_decl = self.inv_decls[func_name]
                mlog.debug("inv_decl: {}".format(inv_decl))
                vars = frame.GetVariables(True, True, True, True)
                dv = dict([(v.GetName(), v.GetValue()) for v in vars])
                trace = func_name + ': ' + (' '.join(map(str, [dv[s.name] for s in inv_decl])))
                mlog.debug("trace: {}".format(trace))
                traces.append(trace)
            process.Continue()
        process.Kill()
        return traces