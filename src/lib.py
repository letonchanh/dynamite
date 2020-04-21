import helpers.vcommon as CM
import z3
import random
import itertools
import sage.all
import math
from pathlib import Path
from data.traces import Inps, Trace, Traces, DTraces
from data.inv.invs import Invs
from utils import settings
from parsers import Z3OutputHandler
from helpers.miscs import Z3, Miscs
import helpers.vcommon as dig_common_helpers
import settings as dig_settings
import data.prog as dig_prog

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
            mlog.debug("inps ({}): {}".format(len(inps), inps))
            prev_len_inps = len(inps)
            new_inps = self.prog.gen_rand_inps(n_needed=n_inps-len(inps))
            inps.merge(new_inps, inp_decls.names)

        mlog.debug("gen {}/{} random inps".format(len(inps), n_inps))
        # mlog.debug("inps: {}".format(inps))
        inps = self._sample_inps(inps)
        return inps

    def get_traces_from_inps(self, rInps):
        inp_decls = self.prog.inp_decls
        inv_decls = self.prog.inv_decls
        rInps = self._sample_inps(rInps)
        raw_traces = self.prog._get_traces_mp(rInps)
        itraces = {}
        for inp, lines in raw_traces.items():
            # dtraces = {}
            itraces.setdefault(inp, {})
            for l in lines:
                # vtrace1: 8460 16 0 1 16 8460
                parts = l.split(':')
                assert len(parts) == 2, parts
                loc, tracevals = parts[0], parts[1]
                loc = loc.strip()  # vtrace1
                ss = inv_decls[loc].names
                vs = tracevals.strip().split()
                trace = Trace.parse(ss, vs)
                # if loc not in dtraces:
                #     dtraces[loc] = [trace]
                # else:
                #     dtraces[loc].append(trace)
                # dtraces.setdefault(loc, []).append(trace)
                itraces[inp].setdefault(loc, []).append(trace)
            # dtraces = DTraces.parse(lines, inv_decls) # Using set, do not preserve order of traces
            # print dtraces.__str__(printDetails=True)
            # itraces[inp] = dtraces
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
            # mlog.debug("{}: {}".format(inp, dtraces.keys()))
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
        # split_index = math.floor((1 - settings.test_ratio)*len(lst))
        split_index = math.floor(len(lst) / 2)
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

class Solver(object):
    def __init__(self, tmpdir):
        self.tmpdir = tmpdir

    def check_sat_and_get_rand_model(self, solver, using_nla=False, range_constrs=[]):
        z3_output_handler = Z3OutputHandler()
        myseed = random.randint(0, 1000000)
        if using_nla:
            theory = 'qfnra'
        else:
            theory = 'qflra'
        
        while True:
            range_constr = None
            if range_constrs:
                range_constr = range_constrs.pop()
                solver.push()
                solver.add(range_constr)

            mlog.debug("range_constr: {}, {} remaining".format(range_constr, len(range_constrs)))
            smt2_str = [
                '(set-option :smt.arith.random_initial_value true)',
                solver.to_smt2().replace('(check-sat)', ''),
                '(check-sat-using (using-params {} :random-seed {}))'.format(theory, myseed),
                '(get-model)']
            smt2_str = '\n'.join(smt2_str)
            # mlog.debug("smt2_str: {}".format(smt2_str))
            filename = self.tmpdir / 't.smt2'
            dig_common_helpers.vwrite(filename, smt2_str)
            cmd = 'z3 {}'.format(filename)
            rmsg, errmsg = dig_common_helpers.vcmd(cmd)
            assert not errmsg, "'{}': {}".format(cmd, errmsg)
            z3_output_ast = z3_output_handler.parser.parse(rmsg)
            chk, model = z3_output_handler.transform(z3_output_ast)
            mlog.debug("chk: {}, : {}".format(chk, model))
            if range_constr is not None:
                solver.pop()
                if chk != z3.sat or not model:
                    # continue to find another valid range
                    continue
            else:
                return chk, model

    def get_models(self, f, k, inp_decls=None, using_random_seed=False):
        if not using_random_seed:
            return Z3.get_models(f, k)

        assert z3.is_expr(f), f
        assert k >= 1, k

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


        solver = Z3.create_solver()
        solver.add(f)

        is_nla = False
        fterms = self.get_mul_terms(f)
        nonlinear_fterms = list(itertools.filterfalse(lambda t: not self.is_nonlinear_mul_term(t), fterms))
        mlog.debug("nonlinear_fterms: {}".format(nonlinear_fterms))
        if nonlinear_fterms:
            is_nla = True

        models = []
        model_stat = {}
        i = 0
        # while solver.check() == z3.sat and i < k:
        while i < k:
            chk, m = self.check_sat_and_get_rand_model(solver, is_nla, range_constrs)
            if chk != z3.sat or not m:
                break
            i = i + 1
            models.append(m)
            for (x, v) in m:
                model_stat.setdefault(x, {})
                c = model_stat[x].setdefault(v, 0)
                model_stat[x][v] = c + 1
            # mlog.debug("model {}: {}".format(i, m))
            # create new constraint to block the current model
            block_m = z3.Not(z3.And([z3.Int(x) == v for (x, v) in m]))
            solver.add(block_m)
            for (x, v) in m:
                if model_stat[x][v] / k > 0.1:
                    block_x = z3.Int(x) != v
                    # mlog.debug("block_x: {}".format(block_x))
                    solver.add(block_x)

        # mlog.debug("model_stat: {}".format(model_stat))
        stat = solver.check()

        if stat == z3.unknown:
            rs = None
        elif stat == z3.unsat and i == 0:
            rs = False
        else:
            rs = models

        assert not (isinstance(rs, list) and not rs), rs
        return rs, stat

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


    # @staticmethod
    # def __is_mul_of_literals(e):
    #     def __is_mul_of_literals_aux(e, seen):
    #         e_id = _get_expr_id(e)
    #         if e_id in seen:
    #             return seen[e_id]
    #         else:
    #             r = z3.is_mul(e) and \
    #                 all(_is_literal_expr(c) or __is_mul_of_literals_aux(c, seen) for c in e.children())
    #             return r
    #     return __is_mul_of_literals_aux(e, {})

    # @staticmethod
    # def __get_mul_terms(e):
    #     def __get_mul_terms_aux(e, seen):
    #         e_id = _get_expr_id(e)
    #         if e_id in seen:
    #             return seen[e_id]
    #         else:
    #             r = []
    #             if z3.is_mul(e):
    #                 for c in e.children():
    #                     if not z3.is_mul(c):
    #                         r.append(c)
    #                     else:
    #                         r = r + __get_mul_terms_aux(c, seen)
    #                 seen[e_id] = r
    #             return r
    #     return __get_mul_terms_aux(e, {})

    # @staticmethod
    # def _is_term_expr(e):
    #     """
    #     x, y = Ints('x y')
    #     Solver._is_term_expr(x) == True
    #     Solver._is_term_expr(IntVal(1)) == True
    #     Solver._is_term_expr(x*y) == True
    #     Solver._is_term_expr(x*y*z) == True
    #     Solver._is_term_expr(x**2) == True
    #     Solver._is_term_expr(2**x) == True
    #     Solver._is_term_expr(x + 1) == False
    #     """
    #     r = _is_var_expr(e) or \
    #         _is_const_expr(e) or \
    #         _is_mul_expr(e) or \
    #         _is_pow_expr(e)
    #     return r

    # @staticmethod
    # def __distribute_mul_over_add(e):
    #     def __distribute_mul_over_add_aux(e, seen):
    #         e_id = _get_expr_id(e)
    #         if e_id in seen:
    #             return seen[e_id]
    #         else:
    #             if is_app_of(e, Z3_OP_UMINUS):
    #                 r = __distribute_mul_over_add_aux((-1)*(e.arg(0)), seen)
    #             elif is_sub(e):
    #                 r = __distribute_mul_over_add_aux(e.arg(0) + (-1)*e.arg(1), seen)
    #             elif is_app(e) and e.num_args() == 2:
    #                 c1 = __distribute_mul_over_add_aux(e.arg(0), seen)
    #                 c2 = __distribute_mul_over_add_aux(e.arg(1), seen)
    #                 if is_add(e):
    #                     r = c1 + c2
    #                 elif is_mul(e):
    #                     if is_add(c1):
    #                         c11 = c1.arg(0)
    #                         c12 = c1.arg(1)
    #                         r = __distribute_mul_over_add_aux(c11*c2 + c12*c2, seen)
    #                     elif is_add(c2):
    #                         c21 = c2.arg(0)
    #                         c22 = c2.arg(1)
    #                         r = __distribute_mul_over_add_aux(c1*c21 + c1*c22, seen)
    #                     else:
    #                         r = c1*c2
    #                 else:
    #                     r = e
    #             else:
    #                 r = e
    #             seen[e_id] = r
    #             return r
    #     return __distribute_mul_over_add_aux(e, {})