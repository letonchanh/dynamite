import z3

import helpers.vcommon as dig_common_helpers
from data.prog import Symb, Symbs
from data.traces import Inps, Inp
from helpers.miscs import Z3

from utils import settings

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

class LoopPart(object):
    def __init__(self, inp_decls, cond, transrel):
        self.inp_decls = inp_decls
        self.cond = cond
        self.transrel = transrel

class Stem(LoopPart):
    def get_initial_inp(self, inp, config):
        assert isinstance(inp, Inp)
        ss = config.inv_decls[config.preloop_loc]
        # inp_decls = Symbs([Symb(s, 'I' if type(v) is int else 'D') for s, v in zip(inp.ss, inp.vs)])
        # vs = [s.expr(settings.use_reals) for s in ss]
        f = z3.And(self.cond, self.transrel, inp.mkExpr(ss.exprs(settings.use_reals)))
        init_symvars = config.symstates.init_symvars
        # mlog.debug("init_symvars ({}): {}".format(type(init_symvars), init_symvars))
        # mlog.debug("inp_decls ({}): {}".format(type(self.inp_decls), self.inp_decls))
        mlog.debug("f: {}".format(f))
        rs, _ = config.solver.get_models(f, 1, settings.use_random_seed)
        mlog.debug("rs: {}".format(rs))
        inps = config.solver.mk_inps_from_models(
                    rs, init_symvars.exprs((settings.use_reals)), config.exe)
        inp_ss = tuple([s for (s, _) in self.inp_decls])
        inps = Inps(set(map(lambda inp: Inp(inp_ss, inp.vs), inps)))
        mlog.debug("inps: {}".format(inps))
        return inps

class Loop(LoopPart):
    pass

class LoopInfo(object):
    def __init__(self, stem, loop):
        self.stem = stem
        self.loop = loop