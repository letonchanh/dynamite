from data.inv.invs import Invs
from data.inv.base import Inv
from utils import settings
from helpers.miscs import Z3
import helpers.vcommon as dig_common_helpers
import z3
import itertools
import functools
from functools import partial

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

class ZFormula(set):
    def __init__(self, fs):
        super(ZFormula, self).__init__(
            map(lambda f: f.expr(settings.use_reals) if isinstance(f, Inv) else f, 
            fs))

    def expr(self):
        if self:
            fs = map(lambda f: f.expr() if isinstance(f, ZFormula) else f, self)
            return self.reduce_op(list(fs))
        else:
            return z3.BoolVal(self.empty_interp())

    def implies(self, conseq):
        fante = self.expr()
        fconseq = conseq.expr()

        models, _ = Z3.get_models(z3.Not(z3.Implies(fante, fconseq)), k=1)
        return models is False

    def is_unsat(self):
        models, _ = Z3.get_models(self.expr(), k=1)
        return models is False

    def simplify(self):
        return Z3.simplify(self.expr())

class ZConj(ZFormula):
    def __init__(self, fs):
        super().__init__(fs)

    @property
    def reduce_op(self):
        return partial(z3.And)

    @property
    def empty_interp(self):
        return False

class ZDisj(ZFormula):
    def __init__(self, fs):
        super().__init__(fs)

    @property
    def reduce_op(self):
        return partial(z3.Or)

    @property
    def empty_interp(self):
        return True

    

    
