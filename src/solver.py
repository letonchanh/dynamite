import z3
import itertools
import random
import math
import sage.all

from utils import settings, logic
import data.prog as dig_prog
import helpers.vcommon as CM
from data.traces import Inps, Trace, Traces
from parsers import Z3OutputHandler
from helpers.miscs import Z3
from utils.profiling import timeit

mlog = CM.getLogger(__name__, settings.logger_level)

class ZSolver(object):
    def __init__(self):
        pass

    def check_sat_and_get_rand_model(self, solver, using_nla=False, range_constrs=[]):
        myseed = random.randint(0, 1000000)

        fst_chk, fst_model = self.check_sat(solver, using_nla, myseed)
        py_chk, py_model = PySMT.py_check_sat(solver, using_nla, myseed)

        assert fst_chk == py_chk, (fst_chk, py_chk)

        if fst_chk == z3.unsat or not range_constrs:
            return fst_chk, fst_model
        
        # sat or unknown, try to find a model in a valid range
        while True:
            range_constr = None
            if range_constrs:
                range_constr = range_constrs.pop()
                solver.push()
                solver.add(range_constr)

            # mlog.debug("range_constr: {}, {} remaining".format(range_constr, len(range_constrs)))
            chk, model = self.check_sat(solver, using_nla, myseed)
            mlog.debug("chk: {}".format(chk))
            mlog.debug("model: {}".format(model))
            
            if range_constr is not None:
                solver.pop()
                if (chk != z3.sat or not model): # and range_constrs
                    # continue to find a model within another range 
                    # or without a range when range_constrs becomes empty
                    # mlog.debug("range_constrs: {}".format(len(range_constrs)))
                    continue
                # elif not range_constrs:
                #     return fst_chk, fst_model
                else:
                    return chk, model
            else: # range_constrs is empty
                return chk, model

    def get_models(self, f, k, inp_decls=None, using_random_seed=False):
        if not using_random_seed:
            return Z3.get_models(f, k)

        assert z3.is_expr(f) or isinstance(f, logic.ZFormula), f
        assert k >= 1, k

        if z3.is_expr(f):
            fe = f
        else:
            fe = f.expr()

        is_nla = False
        fe_terms = self.get_mul_terms(fe)
        fe_nonlinear_terms = list(itertools.filterfalse(lambda t: not self.is_nonlinear_mul_term(t), fe_terms))
        if fe_nonlinear_terms:
            is_nla = True

        mlog.debug("is_nla: {}".format(is_nla))
        # solver = Z3.create_solver()
        solver = self.mk(is_nla)
        # solver = z3.SolverFor('QF_NRA')
        
        pushed_labeled_conj = False

        if isinstance(f, logic.ZConj):
            solver.push()
            pushed_labeled_conj = True
            solver.set(unsat_core=True)
            solver.set(':core.minimize', True)
            for conj in f:
                if isinstance(conj, logic.LabeledExpr):
                    if conj.label:
                        conj_label = conj.label
                    else:
                        conj_label = 'c_' + str(self._get_expr_id(conj.expr))
                    # mlog.debug("conj: {}:{}".format(conj.expr, conj_label))
                    # solver.assert_and_track(conj.expr, conj_label)
                    solver.add(conj.expr)
                else:
                    solver.add(conj)
        else:
            solver.add(fe)
        
        # stat = solver.check()
        # psolver = PySMT()
        stat, _ = PySMT.py_check_sat(solver)
        # stat, _ = self.check_sat(solver, is_nla)
        unsat_core = None

        mlog.debug("stat: {}".format(stat))
        if stat == z3.unknown:
            # mlog.debug("reason_unknown: {}".format(solver.reason_unknown()))
            rs = None
        elif stat == z3.unsat:
            if pushed_labeled_conj:
                unsat_core = solver.unsat_core()
                # mlog.debug("unsat_core: {}".format(unsat_core))
                solver.pop()
                pushed_labeled_conj = False
            rs = False
        else:
            # sat, get k models
            if pushed_labeled_conj:
                solver.pop()
                pushed_labeled_conj = False
                solver.add(fe)

            range_constrs = []
            if inp_decls:
                inp_ranges = list(dig_prog.Prog._get_inp_ranges(len(inp_decls)))
                random.shuffle(inp_ranges)
                # mlog.debug("inp_ranges ({}): {}".format(len(inp_ranges), inp_ranges))
                inp_exprs = inp_decls.exprs(settings.use_reals)
                for inp_range in inp_ranges:
                    range_constr = z3.And([z3.And(ir[0] <= v, v <= ir[1]) for v, ir in zip(inp_exprs, inp_range)])
                    # mlog.debug("range_constr: {}".format(range_constr))
                    range_constrs.append(range_constr)

            models = []
            model_stat = {}
            i = 0
            # while solver.check() == z3.sat and i < k:
            while i < k:
                mlog.debug("{} -> {}".format(i, k))
                chk, m = self.check_sat_and_get_rand_model(solver, is_nla, range_constrs)
                mlog.debug("chk: {}".format(chk))
                mlog.debug("m: {}".format(m))
                if chk != z3.sat or not m:
                    break
                i = i + 1
                models.append(m)
                block_cs = []
                for (x, v) in m:
                    model_stat.setdefault(x, {})
                    if isinstance(v, (int, float)):
                        c = model_stat[x].setdefault(v, 0)
                        model_stat[x][v] = c + 1
                        block_cs.append(z3.Int(x) == v)
                # mlog.debug("model {}: {}".format(i, m))
                # create new constraint to block the current model
                if block_cs:
                    block_c = z3.Not(z3.And(block_cs))
                    solver.add(block_c)
                for (x, v) in m:
                    if model_stat[x][v] / k > 0.1:
                        # block_x = z3.Int(x) != v
                        block_x = z3.Not(z3.Int(x) == v)
                        # mlog.debug("block_x: {}".format(block_x))
                        solver.add(block_x)

            # mlog.debug("models: {}".format(models))

            if models:
                rs = models
            else:
                rs = None
                stat = z3.unknown

        assert not (isinstance(rs, list) and not rs), rs
        return rs, stat, unsat_core

    def mk_inps_from_models(self, models, inp_decls, exe):
        if not models:
            return Inps()
        else:
            assert isinstance(models, list), models
            if all(isinstance(m, z3.ModelRef) for m in models):
                ms, _ = Z3.extract(models)
            else:
                ms = [{x: sage.all.sage_eval(str(v)) for (x, v) in model}
                        for model in models]
            s = set()
            rand_inps = []
            for m in ms:
                inp = []
                for v in inp_decls:
                    sv = str(v)
                    if sv in m:
                        inp.append(m[sv])
                    else:
                        if not rand_inps:
                            rand_inps = exe.gen_rand_inps(len(ms))
                            mlog.debug("rand_inps: {} - {}\n{}".format(len(ms), len(rand_inps), rand_inps))
                        rand_inp = rand_inps.pop()
                        d = dict(zip(rand_inp.ss, rand_inp.vs))
                        inp.append(sage.all.sage_eval(str(d[sv])))
                s.add(tuple(inp))
            inps = Inps()
            inps.merge(s, tuple(inp_decls))
            return inps

    # Internal static methods over z3's ast
    @classmethod
    def _get_expr_id(cls, e):
        # r = z3.Z3_get_ast_hash(e.ctx.ref(), e.ast)
        r = e.hash()
        return r

    @classmethod
    def _transform_expr(cls, f, e):
        def cache(_f, e, seen):
            e_id = cls._get_expr_id(e)
            if e_id in seen:
                return seen[e_id]
            else:
                r = _f(cache, e, seen)
                seen[e_id] = r
                return r

        def no_cache(_f, e, seen):
            return _f(cache, e, seen)

        r = f(cache, e, {})
        return r

    @classmethod
    def _is_var_expr(cls, e):
        r = z3.is_const(e) and \
            e.decl().kind() == z3.Z3_OP_UNINTERPRETED
        return r

    @classmethod
    def _is_const_expr(cls, e):
        def f(_cache, e, seen):
            def f_cache(e):
                return _cache(f, e, seen)

            r = (z3.is_const(e) and e.decl().kind() == z3.Z3_OP_ANUM) or \
                (e.num_args() > 0 and all(f_cache(c) for c in e.children()))
            return r
        return cls._transform_expr(f, e)

    @classmethod
    def _is_literal_expr(cls, e):
        return cls._is_var_expr(e) or cls._is_const_expr(e)

    @classmethod
    def _is_pow_expr(cls, e):
        return z3.is_app_of(e, z3.Z3_OP_POWER)

    @classmethod
    def _is_mul_of_literals(e):
        def f(_cache, e, seen):
            def f_cache(e):
                return _cache(f, e, seen)

            r = z3.is_mul(e) and \
                all(cls._is_literal_expr(c) or f_cache(c) for c in e.children())
            return r
        return cls._transform_expr(f, e)

    @classmethod
    def _get_op_terms(cls, is_op, e):
        def f(_cache, e, seen):
            def f_cache(e):
                return _cache(f, e, seen)

            r = []
            if is_op(e):
                for c in e.children():
                    if not is_op(c):
                        r.append(c)
                    else:
                        r = r + f_cache(c)
            else:
                r.append(e)
            return r
        return cls._transform_expr(f, e)

    @classmethod
    def _get_mul_terms(cls, e):
        """
        _get_mul_terms(x*y*(z+1)) == [x, y, z+1]
        """
        return cls._get_op_terms(z3.is_mul, e)

    @classmethod
    def _get_add_terms(cls, e):
        """
        _get_add_terms(x*y + y*z) == [x*y, y*z]
        """
        return cls._get_op_terms(z3.is_add, e)

    @classmethod
    def _distribute_mul_over_add(cls, e):
        def f(_cache, e, seen):
            def f_cache(e):
                return _cache(f, e, seen)

            if z3.is_app_of(e, z3.Z3_OP_UMINUS):
                return f_cache((-1)*(e.arg(0)))
            elif z3.is_sub(e):
                return f_cache(e.arg(0) + (-1)*e.arg(1))
            elif z3.is_app(e) and e.num_args() == 2:
                c1 = f_cache(e.arg(0))
                c2 = f_cache(e.arg(1))
                if z3.is_add(e):
                    return c1 + c2
                elif z3.is_mul(e):
                    if z3.is_add(c1):
                        c11 = c1.arg(0)
                        c12 = c1.arg(1)
                        return f_cache(c11*c2 + c12*c2)
                    elif z3.is_add(c2):
                        c21 = c2.arg(0)
                        c22 = c2.arg(1)
                        return f_cache(c1*c21 + c1*c22)
                    else:
                        return c1*c2
                else:
                    return e
            else:
                return e
        return cls._transform_expr(f, e)

    @classmethod
    def get_mul_terms(cls, e):
        Z3_LOGICAL_OPS = [
            z3.Z3_OP_ITE,
            z3.Z3_OP_AND,
            z3.Z3_OP_OR,
            z3.Z3_OP_IFF,
            z3.Z3_OP_XOR,
            z3.Z3_OP_NOT,
            z3.Z3_OP_IMPLIES]
        Z3_REL_OPS = [
            z3.Z3_OP_EQ,
            z3.Z3_OP_DISTINCT,
            z3.Z3_OP_LE,
            z3.Z3_OP_LT,
            z3.Z3_OP_GE,
            z3.Z3_OP_GT]

        def f(_cache, e, seen):
            def f_cache(e):
                return _cache(f, e, seen)
            
            r = []
            if z3.is_app(e):
                if e.decl().kind() in Z3_LOGICAL_OPS + Z3_REL_OPS:
                    for c in e.children():
                        r = r + f_cache(c)
                elif z3.is_arith(e):
                    e = cls._distribute_mul_over_add(e)
                    r = r + cls._get_add_terms(e)
            return r
        return cls._transform_expr(f, e)

    @classmethod
    def is_nonlinear_mul_term(cls, e):
        ts = cls._get_mul_terms(e)
        # mlog.debug("ts: {}".format(ts))
        ts = list(itertools.filterfalse(lambda t: cls._is_const_expr(t), ts))
        # mlog.debug("ts: {}".format(ts))
        r = len(ts) >= 2 or \
            len(ts) == 1 and cls._is_pow_expr(ts[0])
        # mlog.debug("e: {}: {}".format(e, r))
        return r

class Z3Bin(ZSolver):
    def __init__(self, tmpdir):
        self.tmpdir = tmpdir

    def mk(self, using_nla=False, myseed=None):
        return z3.Solver()

    def check_sat(self, zsolver, using_nla=False, myseed=None):
        z3_output_handler = Z3OutputHandler()
        if using_nla:
            int_theory = 'qfnia'
            real_theory = 'qfnra'
        else:
            int_theory = 'qflia'
            real_theory = 'qflra'
        ti = '(using-params {} :random-seed {})'.format(int_theory, myseed)
        tr = '(using-params {} :random-seed {})'.format(real_theory, myseed)
        t = '(par-or {} {})'.format(ti, tr)
        smt2_str = [
            '(set-option :smt.arith.random_initial_value true)',
            zsolver.to_smt2().replace('(check-sat)', ''),
            # '(check-sat-using (using-params {} :random-seed {}))'.format(theory, myseed),
            '(check-sat-using {})'.format(t),
            '(get-model)']
        smt2_str = '\n'.join(smt2_str)
        # mlog.debug("smt2_str: {}".format(smt2_str))
        filename = self.tmpdir / 't.smt2'
        CM.vwrite(filename, smt2_str)
        cmd = 'z3 {}'.format(filename)
        rmsg, errmsg = CM.vcmd(cmd)
        # mlog.debug("rmsg: {}".format(rmsg))
        # mlog.debug("errmsg: {}".format(errmsg))
        assert not errmsg, "'{}': {}".format(cmd, errmsg)
        z3_output_ast = z3_output_handler.parser.parse(rmsg)
        chk, model = z3_output_handler.transform(z3_output_ast)
        # mlog.debug("chk: {}, : {}".format(chk, model))
        return chk, model

class Z3Py(ZSolver):
    def __init__(self):
        pass

    @classmethod
    def mk(cls, using_nla=False, myseed=None):
        if using_nla:
            int_theory = 'qfnia' # qfnra
            real_theory = 'qfnra'
        else:
            int_theory = 'qflia' # qflia
            real_theory = 'qflra'

        ti = z3.Tactic(int_theory)
        tr = z3.Tactic(real_theory)

        if myseed:
            z3.set_param('smt.arith.random_initial_value', True)
            p = z3.ParamsRef()
            p.set("random-seed", myseed)
            ti = z3.WithParams(ti, p)
            tr = z3.WithParams(tr, p)

        t = z3.ParOr(ti, tr)
        t = z3.TryFor(t, settings.SOLVER_TIMEOUT)
        return t.solver()

    @classmethod
    @timeit
    def check_sat(cls, zsolver, using_nla=False, myseed=None):
        tsolver = cls.mk(using_nla, myseed)
        # mlog.debug("t_solver: {}".format(t_solver.param_descrs()))
        # pds = t_solver.param_descrs()
        # for i in range(pds.size()):
        #     pd = pds.get_name(i)
        #     if 'random' in pd:
        #         mlog.debug("pds[{}]: {}".format(i, pd))
        tsolver.add(zsolver.assertions())
        chk = tsolver.check()
        model = None
        if chk == z3.sat:
            m = tsolver.model() # <class 'z3.z3.ModelRef'>
            # (<class 'z3.z3.FuncDeclRef'>, <class 'z3.z3.IntNumRef'>) list
            model = [(v.name(), m[v].as_long()) for v in m.decls()]
        return chk, model

from pysmt.shortcuts import Portfolio, Solver, Symbol
from pysmt.typing import INT, REAL
from pysmt.oracles import get_logic
class PySMT(ZSolver):
    def __init__(self):
        pass

    @classmethod
    def mk(cls, using_nla, myseed=None):
        return z3.Solver()

    @classmethod
    @timeit
    def py_check_sat(cls, zsolver, using_nla=False, myseed=None):
        zlogic = 'QF_NIA' if using_nla else 'QF_LIA'
        solver_opts = {"random_seed": myseed} if myseed else {}
        zf = z3.And(zsolver.assertions())

        @timeit
        def _convert(zf):
            zvs = z3.z3util.get_vars(zf)
            vs = [Symbol(v.decl().name(), 
                INT if v.is_int() else REAL) for v in zvs]
            z3s = Solver(name='z3', 
                        logic=zlogic,
                        random_seed=myseed,
                        generate_models=True)
            f = z3s.converter.back(zf)
            return vs, f

        vs, f = _convert(zf)
        f_logic = get_logic(f)

        @timeit
        def _solve(f):
            with Portfolio([
                    # ("cvc4", solver_opts),
                    ("z3", solver_opts),
                    # ("yices", solver_opts)
                    ],
                    logic=f_logic,
                    incremental=False,
                    generate_models=True) as solver:
            # with z3s as solver:
                solver.add_assertion(f)
                model = []
                try:
                    # mlog.debug("PySMT: solving {}".format(f))
                    r = solver.solve()
                    # mlog.debug("r: {}".format(r))
                    if r:
                        # for v in vs:
                        #     # mv = solver.get_value(v).constant_value()
                        #     mv = solver.get_py_value(v)
                        #     model.append((v.symbol_name(), int(mv)))
                        py_model = solver.get_model()
                        model = [(v.symbol_name(), int(py_model.get_py_value(v))) for v in vs]
                    # mlog.debug("model: {}".format(model))
                    return (z3.sat if r else z3.unsat), model
                except Exception as e:
                    mlog.debug("check_sat: {}".format(e))
                    return z3.unknown, []

        return _solve(f)

