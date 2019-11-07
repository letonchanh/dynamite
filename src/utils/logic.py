from data.inv.invs import Invs
from utils import settings
from helpers.miscs import Z3
import z3
import itertools
import functools


class ZInvs(set):
    def __init__(self, invs):
        assert isinstance(invs, Invs), invs
        super(ZInvs, self).__init__(map(lambda inv: inv.expr(settings.use_reals), invs))

    def expr(self):
        if self:
            return functools.reduce(z3.And, self)
        else:
            return z3.BoolVal(False)

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