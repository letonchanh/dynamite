import helpers.vcommon as CM
from data.traces import Inps, Trace, DTraces
from data.inv.invs import Invs
from utils import settings

mlog = CM.getLogger(__name__, settings.logger_level)


class Execution(object):
    def __init__(self, prog):
        self.prog = prog

    def get_rand_traces(self):
        inps = Inps()
        rInps = self.prog.gen_rand_inps(100)
        inp_decls = self.prog.inp_decls
        inv_decls = self.prog.inv_decls
        mlog.debug("gen {} random inps".format(len(rInps)))
        rInps = inps.merge(rInps, inp_decls.names)
        raw_traces = self.prog._get_traces_mp(rInps)
        itraces = {}
        for inp, lines in raw_traces.items():
            dtraces = {}
            for l in lines:
                # vtrace1: 8460 16 0 1 16 8460
                parts = l.split(':')
                assert len(parts) == 2, parts
                loc, tracevals = parts[0], parts[1]
                loc = loc.strip()  # vtrace1
                ss = inv_decls[loc].names
                vs = tracevals.strip().split()
                trace = Trace.parse(ss, vs)
                if loc not in dtraces:
                    dtraces[loc] = [trace]
                else:
                    dtraces[loc].append(trace)
            # print dtraces.__str__(printDetails=True)
            itraces[inp] = dtraces
        return itraces


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
            mlog.debug("{}: {}".format(inp, dtraces.keys()))
            chains = dtraces.keys()
            if self.postloop in chains:
                if self.inloop in chains:
                    term_inps.append(inp)
                else:
                    base_term_inps.append(inp)
            else:
                mayloop_inps.append(inp)
        return base_term_inps, term_inps, mayloop_inps

class Inference(object):
    def __init__(self, inv_decls, seed, maxdeg=1):
        self.seed = seed
        self.maxdeg = maxdeg
        self.inv_decls = inv_decls

    def infer_from_traces(self, itraces, traceid, inps={}):
        try:
            dtraces = DTraces()
            if not inps:
                inps = itraces.keys()
            for inp in inps:
                traces = itraces[inp]
                if traceid in traces:
                    for trace in traces[traceid]:
                        dtraces.add(traceid, trace)
            mlog.debug("dtraces: {}".format(dtraces.__str__(printDetails=False)))
            import alg as dig_alg
            dig = dig_alg.DigTraces.from_dtraces(self.inv_decls, dtraces)
            dtraces.vwrite(self.inv_decls, traceid + '.tcs')
            invs, traces, tmpdir = dig.start(self.seed, self.maxdeg)
            mlog.debug("invs: {}".format(invs)) # <class 'data.inv.invs.DInvs'>
            return invs[traceid]
        except AssertionError:
            return Invs()
