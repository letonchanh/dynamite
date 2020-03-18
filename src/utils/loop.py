import z3

import helpers.vcommon as dig_common_helpers
from data.prog import Symb, Symbs
from data.traces import Inp
from helpers.miscs import Z3

from utils import settings

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

class LoopPart(object):
    def __init__(self, inp_decls, cond, transrel):
        self.inp_decls = inp_decls
        self.cond = cond
        self.transrel = transrel

class Stem(LoopPart):
    def get_initial_inp(self, inp, ss):
        assert isinstance(inp, Inp)
        mlog.debug("inp: {} - {}".format(inp, inp.mkExpr(inp.ss)))
        # inp_decls = Symbs([Symb(s, 'I' if type(v) is int else 'D') for s, v in zip(inp.ss, inp.vs)])
        vs = [s.expr(settings.use_reals) for s in ss]
        f = Z3.qe(z3.Exists(vs, z3.And(self.cond, self.transrel, 
                                       inp.mkExpr(ss.exprs(settings.use_reals)))))
        mlog.debug("f: {}".format(f))

class Loop(LoopPart):
    pass

class LoopInfo(object):
    def __init__(self, stem, loop):
        self.stem = stem
        self.loop = loop