import helpers.vcommon as CM
import z3
import random
import math
from pathlib import Path
from collections import defaultdict 

from data.traces import Inp, Inps, Trace, Traces, DTraces
from data.inv.invs import Invs
from helpers.miscs import Z3, Miscs
import helpers.vcommon as dig_common_helpers
import settings as dig_settings
import data.prog as dig_prog

from utils import settings
from utils.profiling import timeit

mlog = CM.getLogger(__name__, settings.logger_level)

class Execution(object):
    def __init__(self, prog):
        self.prog = prog

    def _sample_inps(self, inps):
        inps_threshold = settings.inps_threshold * (1 + settings.test_ratio)
        max_inps = math.ceil(inps_threshold * settings.n_inps)
        if len(inps) > max_inps:
            import random
            inps = Inps(set(random.sample(inps, max_inps)))
            mlog.debug("reduced inps: {}".format(len(inps)))
        return inps

    def gen_rand_inps(self, n_inps):
        inps = Inps()
        inp_decls = self.prog.inp_decls
        prev_len_inps = -1
        while prev_len_inps < len(inps) and len(inps) < n_inps:
            # mlog.debug("inps ({}): {}".format(len(inps), inps))
            prev_len_inps = len(inps)
            new_inps = self.prog.gen_rand_inps(n_needed=n_inps-len(inps))
            inps.merge(new_inps, inp_decls.names)

        mlog.debug("gen {}/{} random inps".format(len(inps), n_inps))
        # mlog.debug("inps: {}".format(inps))
        inps = self._sample_inps(inps)
        return inps

    @timeit
    def get_traces_from_inps(self, inps):
        inp_decls = self.prog.inp_decls
        inv_decls = self.prog.inv_decls
        # inps = self._sample_inps(inps)

        mlog.debug('inp_decls: {}'.format(inp_decls))
        mlog.debug('inv_decls: {}'.format(inv_decls))

        @timeit
        def _get_traces_mp(inps):
            return self.prog._get_traces_mp(inps)
        raw_traces = _get_traces_mp(inps)

        @timeit
        def _merge_traces():
            # def f(task):
            #     inp, l = task
            #     # vtrace1: 8460 16 0 1 16 8460
            #     parts = l.split(':')
            #     assert len(parts) == 2, parts
            #     loc, tracevals = parts[0], parts[1]
            #     loc = loc.strip()  # vtrace1
            #     ss = inv_decls[loc].names
            #     vs = tracevals.strip().split()
            #     trace = Trace.parse(ss, vs)
            #     return (inp, loc, trace)

            # tasks = [(inp, l) for inp, lines in raw_traces.items() for l in lines]
            # wrs = Miscs.run_mp_ex("merge traces", tasks, f)
            # itraces = defaultdict(dict)
            # for inp, loc, trace in wrs:
            #     itraces[inp].setdefault(loc, []).append(trace)
            # return itraces

            def f(task):
                inp, lines = task
                dtraces = defaultdict(list)
                for l in lines:
                    # vtrace1: 8460 16 0 1 16 8460
                    parts = l.split(':')
                    assert len(parts) == 2, parts
                    loc, tracevals = parts[0], parts[1]
                    loc = loc.strip()  # vtrace1
                    ss = inv_decls[loc].names
                    vs = tracevals.strip().split()
                    trace = Trace.parse(ss, vs)
                    dtraces[loc].append(trace)
                return (inp, dtraces)

            tasks = raw_traces.items()
            wrs = Miscs.run_mp_ex("merge traces", tasks, f)
            itraces = {inp: dtraces for inp, dtraces in wrs}
            return itraces

            # def f(task):
            #     import os
            #     pid = os.getpid()
            #     inp, lines = task
            #     ltraces = defaultdict(list)
            #     ptraces = defaultdict(dict)
            #     itraces = defaultdict()
            #     # mlog.debug('inp: {}'.format(inp))
            #     for l in lines:
            #         # vtrace1: 8460 16 0 1 16 8460
            #         parts = l.split(':')
            #         assert len(parts) == 2, parts
            #         loc, tracevals = parts[0], parts[1]
            #         loc = loc.strip()  # vtrace1_20
            #         ss = inv_decls[loc].names
            #         vs = tracevals.strip().split()
            #         trace = Trace.parse(ss, vs)
            #         if '_' in loc:
            #             lparts = loc.split('_')
            #             indicator, pos = lparts[0], lparts[1] # vtrace1, 20
            #             # mlog.debug('{}: loc, indicator, pos: {}, {}, {}'.format(pid, loc, indicator, pos))
            #             if indicator == (dig_settings.TRACE_INDICATOR + str(settings.VTRACE.PRELOOP_LABEL)):
            #                 prev_trace = ptraces[pos]
            #                 if prev_trace:
            #                     prev_inp = Inp(ss, prev_trace[loc][0].vs)
            #                     if prev_inp not in itraces:
            #                         itraces[prev_inp] = prev_trace
            #                 ptraces[pos] = defaultdict(list)
            #                 ptraces[pos][loc] = [trace]
            #             else:
            #                 ptraces[pos][loc].append(trace)
            #         else:
            #             ltraces[loc].append(trace)
            #     if itraces or ptraces:
            #         for pos in ptraces:
            #             last_trace = ptraces[pos]
            #             if last_trace:
            #                 loc = dig_settings.TRACE_INDICATOR + str(settings.VTRACE.PRELOOP_LABEL) + '_' + pos
            #                 last_inp = Inp(ss, last_trace[loc][0].vs)
            #                 if last_inp not in itraces:
            #                     itraces[last_inp] = last_trace
            #         return [(inp, dtraces) for inp, dtraces in itraces.items()]
            #     else:
            #         return [(inp, ltraces)]      

            # tasks = raw_traces.items()
            # wrs = Miscs.run_mp_ex("merge traces", tasks, f)
            # # wrs = []
            # # for task in tasks:
            # #     wrs.append(f(task))
            # itraces = {inp: dtraces for wr in wrs for inp, dtraces in wr}
            # return itraces

            # itraces = {}
            # for inp, lines in raw_traces.items():
            #     # dtraces = {}
            #     itraces.setdefault(inp, {})
            #     for l in lines:
            #         # vtrace1: 8460 16 0 1 16 8460
            #         parts = l.split(':')
            #         assert len(parts) == 2, parts
            #         loc, tracevals = parts[0], parts[1]
            #         loc = loc.strip()  # vtrace1
            #         ss = inv_decls[loc].names
            #         vs = tracevals.strip().split()
            #         trace = Trace.parse(ss, vs)
            #         # if loc not in dtraces:
            #         #     dtraces[loc] = [trace]
            #         # else:
            #         #     dtraces[loc].append(trace)
            #         # dtraces.setdefault(loc, []).append(trace)
            #         itraces[inp].setdefault(loc, []).append(trace)
            #     # dtraces = DTraces.parse(lines, inv_decls) # Using set, do not preserve order of traces
            #     # print dtraces.__str__(printDetails=True)
            #     # itraces[inp] = dtraces
            # return itraces

        return _merge_traces()

class Classification(object):
    def __init__(self, preloop, inloop, postloop):
        self.preloop = preloop
        self.inloop = inloop
        self.postloop = postloop

    def classify_inps(self, itraces):
        base_term_inps = []
        term_inps = []
        mayloop_inps = []
        for inp, dtraces in itraces.items():
            # mlog.debug("{}: {}".format(inp, dtraces.keys()))
            chains = dtraces.keys()
            if self.preloop in chains:
                if self.postloop in chains:
                    if self.inloop in chains:
                        term_inps.append(inp)
                    else:
                        base_term_inps.append(inp)
                else:
                    mayloop_inps.append(inp)
        return base_term_inps, term_inps, mayloop_inps

    @classmethod
    def print_inps(cls, itraces):
        for inp, dtraces in itraces.items():
            mlog.debug('{}'.format(list(map(lambda k: (k, len(dtraces[k])), dtraces.keys()))))

class Inference(object):
    def __init__(self, inv_decls, seed, tmpdir):
        self.seed = seed
        self.inv_decls = inv_decls
        self.tmpdir = tmpdir

    def get_traces_by_id(self, itraces, traceid, inps=None):
        dtraces = DTraces()
        if inps is None:
            inps = itraces.keys()
        traces = Traces()
        for inp in inps:
            inp_traces = itraces[inp]
            if traceid in inp_traces:
                for trace in inp_traces[traceid]:
                    traces.add(trace)
        max_len = settings.inps_threshold * settings.n_inps
        if len(traces) > max_len:
            traces = Traces(set(random.sample(traces, max_len)))
        dtraces[traceid] = traces
        mlog.debug("dtraces[{}]: {}".format(traceid, dtraces[traceid].__str__(printDetails=False)))
        # dtraces.vwrite(self.inv_decls, self.tmpdir / (traceid + '.tcs'))
        return dtraces

    @classmethod
    def _split(cls, lst):
        random.shuffle(lst)
        split_index = math.floor((1 - settings.test_ratio)*len(lst))
        # split_index = math.floor(len(lst) / 2)
        return lst[:split_index], lst[split_index:]

    def infer_from_traces(self, itraces, traceid, inps=None, maxdeg=1, simpl=False):
        r = None
        old_do_simplify = dig_settings.DO_SIMPLIFY
        dig_settings.DO_SIMPLIFY = simpl
        
        try:
            train_inps, test_inps = self._split(inps)
            train_dtraces = self.get_traces_by_id(itraces, traceid, train_inps)
            test_dtraces = self.get_traces_by_id(itraces, traceid, test_inps)
            
            import alg as dig_alg
            dig = dig_alg.DigTraces.from_dtraces(self.inv_decls, train_dtraces, test_dtraces)    
            invs, traces = dig.start(self.seed, maxdeg)
            mlog.debug("invs: {}".format(invs)) # <class 'data.inv.invs.DInvs'>
            if traceid in invs:
                r = invs[traceid]
            else:
                r = Invs()
        except Exception as e:
            mlog.debug("exception: {}".format(e))
            pass
        finally:
            dig_settings.DO_SIMPLIFY = old_do_simplify
        return r