import helpers.vcommon as CM
import z3
import random
import sage.all
from pathlib import Path
from data.traces import Inps, Trace, DTraces
from data.inv.invs import Invs
from utils import settings
from parsers import Z3OutputHandler
from helpers.miscs import Z3, Miscs
import helpers.vcommon as dig_common_helpers

mlog = CM.getLogger(__name__, settings.logger_level)

class Execution(object):
    def __init__(self, prog):
        self.prog = prog

    def gen_rand_inps(self, nInps):
        inps = Inps()
        inp_decls = self.prog.inp_decls
        rInps = self.prog.gen_rand_inps(nInps)
        mlog.debug("gen {} random inps".format(len(rInps)))
        # mlog.debug("gen inps: {}".format(rInps))
        rInps = inps.merge(rInps, inp_decls.names)
        return rInps

    def get_traces(self, rInps):
        inp_decls = self.prog.inp_decls
        inv_decls = self.prog.inv_decls
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
            # dtraces = DTraces.parse(lines, inv_decls) # Using set, do not preserve order of traces
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
        # try:
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
            dtraces.vwrite(self.inv_decls, Path(traceid + '.tcs'))
            invs, traces = dig.start(self.seed, self.maxdeg)
            mlog.debug("invs: {}".format(invs)) # <class 'data.inv.invs.DInvs'>
            return invs[traceid]
        # except KeyError, AssertionError:
        #     return Invs()

class Solver(object):
    def __init__(self):
        pass

    @classmethod
    def check_sat_and_get_rand_model(cls, tmpdir, solver):
        z3_output_handler = Z3OutputHandler()
        myseed = random.randint(0, 1000000)
        smt2_str = [
            '(set-option :smt.arith.random_initial_value true)',
            solver.to_smt2().replace('(check-sat)', ''),
            '(check-sat-using (using-params qflra :random-seed {}))'.format(myseed),
            '(get-model)']
        smt2_str = '\n'.join(smt2_str)
        # mlog.debug("smt2_str: {}".format(smt2_str))
        filename = tmpdir + 't.smt2'
        dig_common_helpers.vwrite(filename, smt2_str)
        cmd = 'z3 {}'.format(filename)
        rmsg, errmsg = dig_common_helpers.vcmd(cmd)
        assert not errmsg, "'{}': {}".format(cmd, errmsg)
        z3_output_ast = z3_output_handler.parser.parse(rmsg)
        chk, model = z3_output_handler.transform(z3_output_ast)
        # mlog.debug("model: {}".format(model))
        return chk, model

    @classmethod
    def get_models(cls, f, k, tmpdir, using_random_seed=False):
        if not using_random_seed:
            return Z3.get_models(f, k)

        assert z3.is_expr(f), f
        assert k >= 1, k

        solver = Z3.create_solver()
        solver.add(f)

        models = []
        i = 0
        # while solver.check() == z3.sat and i < k:
        while i < k:
            chk, m = cls.check_sat_and_get_rand_model(tmpdir, solver)
            if chk != z3.sat:
                break
            i = i + 1
            if not m:  # if m == []
                break
            models.append(m)
            # mlog.debug("model {}: {}".format(i, m))
            # create new constraint to block the current model
            block = z3.Not(z3.And([z3.Int(x) == v for (x, v) in m]))
            solver.add(block)

        stat = solver.check()

        if stat == z3.unknown:
            rs = None
        elif stat == z3.unsat and i == 0:
            rs = False
        else:
            rs = models

        assert not (isinstance(rs, list) and not rs), rs
        return rs, stat
