from data.inv.invs import Invs
from data.inv.base import Inv
from helpers.miscs import Z3
from lib import Solver
from utils import settings
import helpers.vcommon as dig_common_helpers
import z3
import itertools
import functools
from functools import partial

mlog = dig_common_helpers.getLogger(__name__, settings.logger_level)

class LabeledExpr(object):
    def __init__(self, expr, label=None):
        assert z3.is_expr(expr) or isinstance(expr, LabeledExpr), expr
        if z3.is_expr(expr):
            self.expr = expr
        else:
            self.expr = expr.expr
        if label:
            self.label = label
        elif z3.is_expr(expr):
            self.label = None
        else:
            self.label = expr.label

    def __repr__(self):
        return "{}:{}".format(self.expr, self.label)

    @classmethod
    def map(cls, f, e):
        assert z3.is_expr(e) or isinstance(e, LabeledExpr)
        if z3.is_expr(e):
            return f(e)
        else:
            return LabeledExpr(f(e.expr), e.label)

    @classmethod
    def map_expr(cls, f, e):
        assert z3.is_expr(e) or isinstance(e, LabeledExpr)
        if z3.is_expr(e):
            return f(e)
        else:
            return f(e.expr)

# Set of z3 formulas
class ZFormula(set):
    def __init__(self, fs):
        if fs is None:
            fs = []
        super(ZFormula, self).__init__(
            map(lambda f: f.expr(settings.use_reals) if isinstance(f, Inv) else f, 
            fs))

    def expr(self):
        if self:
            fs = list(map(lambda f: f.expr() if isinstance(f, ZFormula) 
                                    else LabeledExpr.map_expr(lambda e: e, f), 
                          self))
            if len(self) == 1:
                return fs[0]
            else:
                return self.reduce_op(fs)
        else:
            return z3.BoolVal(self.empty_interp)

    def negate(self):
        if self:
            fs = map(lambda f: f.expr() if isinstance(f, ZFormula) 
                               else LabeledExpr.map_expr(lambda e: e, f), 
                     self)
            nfs = map(lambda f: z3.Not(f), fs)
            return self.negate_cls(list(nfs))
        else:
            return z3.BoolVal(not self.empty_interp)

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

    @classmethod
    def substitue(cls, zf, sst):
        zfs = list(map(lambda f: cls.substitue(f, sst) if isinstance(f, ZFormula) 
                                 else LabeledExpr.map(lambda e: z3.substitute(e, sst), f), 
                       zf))
        return zf.__class__(zfs)

    @classmethod
    def label(cls, zf, mk_label):
        zfs = list(map(lambda f: cls.label(f, mk_label) if isinstance(f, ZFormula)
                                 else LabeledExpr(f, mk_label(f)),
                       zf))
        return zf.__class__(zfs)

class ZConj(ZFormula):
    def __init__(self, fs):
        super().__init__(fs)

    @property
    def reduce_op(self):
        return partial(z3.And)

    @property
    def empty_interp(self):
        return False

    @property
    def negate_cls(self):
        return partial(ZDisj)

class ZDisj(ZFormula):
    def __init__(self, fs):
        super().__init__(fs)

    @property
    def reduce_op(self):
        return partial(z3.Or)

    @property
    def empty_interp(self):
        return True

    @property
    def negate_cls(self):
        return partial(ZConj)

    

    
