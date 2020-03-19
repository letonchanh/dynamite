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
    def get_initial_cond(self, f, config):
        init_symvars = (config.symstates.init_symvars).exprs(settings.use_reals)
        init_f = z3.And(self.cond, self.transrel, f)
        init_f_vars = Z3.get_vars(init_f)
        exists_vars = init_f_vars.difference(init_symvars)
        init_cond = z3.Exists(list(exists_vars), init_f)
        mlog.debug("init_cond: {}".format(init_cond))
        qe_init_cond = Z3.qe(init_cond)
        mlog.debug("qe_init_cond: {}".format(qe_init_cond))
        return qe_init_cond

    def get_initial_inp(self, inp, config):
        assert isinstance(inp, Inp)
        ss = config.inv_decls[config.preloop_loc]
        # inp_decls = Symbs([Symb(s, 'I' if type(v) is int else 'D') for s, v in zip(inp.ss, inp.vs)])
        inp_f = inp.mkExpr(ss.exprs(settings.use_reals))
        # f = z3.And(self.cond, self.transrel, inp_f)
        f = self.get_initial_cond(inp_f, config)
        mlog.debug("f: {}".format(f))
        rs, _ = config.solver.get_models(f, 1, settings.use_random_seed)
        mlog.debug("rs: {}".format(rs))
        init_symvars = config.symstates.init_symvars
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