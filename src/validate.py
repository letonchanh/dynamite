import os
import re
import traceback
import shutil
import z3
from pathlib import Path
from functools import partial
import helpers.vcommon as CM
from helpers.miscs import Miscs
import data.traces
from utils import settings
from collections import defaultdict

mlog = CM.getLogger(__name__, settings.logger_level)

class Validator(object):
    def __init__(self, tmpdir):
        mytempdir = tmpdir / self.short_name
        if not mytempdir.exists():
            mytempdir.mkdir()
        self.tmpdir = mytempdir
        self.output_dir = None

    @property
    def witness(self):
        return self.tmpdir / self.witness_filename

    def prove_reach(self, vs, input):
        cwd = os.getcwd()
        res = None
        cex = None
        try:
            os.chdir(self.tmpdir)
            assert input.is_file(), input
            if self.output_dir and self.output_dir.is_dir():
                shutil.rmtree(self.output_dir)

            pcmd = self.prove_reach_cmd(input=input)
            mlog.debug("pcmd: {}".format(pcmd))
            rmsg, errmsg = CM.vcmd(pcmd)
            # assert not errmsg, "'{}': {}".format(pcmd, errmsg)
            mlog.debug("rmsg: {}".format(rmsg))
            res = self.parse_rmsg(rmsg)
            mlog.debug("res: {}".format(res))
            if res is False:
                cex = self.validate_witness(vs, input, expected_result=res)
                mlog.debug('validate_witness: DONE')
                mlog.debug('cex.trans_cex: {}'.format(cex.trans_cex))
        except Exception as ex:
            mlog.debug("Exception: {}".format(ex))
            mlog.debug(traceback.format_exc())
        finally:
            os.chdir(cwd)
            return res, cex

    def validate_witness(self, vs, input, expected_result=False):
        assert self.witness.is_file(), self.witness
        vcmd = self.validate_witness_cmd(input=input)
        mlog.debug("vcmd: {}".format(vcmd))
        v_rmsg, v_errmsg = CM.vcmd(vcmd)
        # assert not v_errmsg, "'{}': {}".format(vcmd, v_errmsg)
        mlog.debug("v_rmsg: {}".format(v_rmsg))
        # mlog.debug("v_errmsg: {}".format(v_errmsg))
        v_res = self.parse_rmsg(v_rmsg)
        assert v_res is expected_result, v_res

        cex = self.mk_cex(vs)

        cex_file = self.tmpdir / self.cex_filename
        assert cex_file.is_file(), cex_file
        cex.mk_trans_cex(cex_file)

        if self.cex_smtlib_filename:
            smtlib_file = self.tmpdir / self.cex_smtlib_filename
            assert smtlib_file.is_file(), smtlib_file
            cex.mk_symb_cex(smtlib_file)
        return cex

    # def _get_substring(self, s, start_indicator, end_indicator=None):
    #     start_index = s.find(start_indicator)
    #     if start_index != -1:
    #         if end_indicator:
    #             end_index = s.find(end_indicator)
    #             if end_index != -1:
    #                 return s[(start_index + len(start_indicator)):end_index]
    #             else:
    #                 return s[(start_index + len(start_indicator)):]
    #         else:
    #             return s[(start_index + len(start_indicator)):]
    #     else:
    #         return None

    def parse_rmsg(self, rmsg):
        # res = self._get_substring(rmsg, self.res_keyword)
        # mlog.debug("res: {}".format(res))
        regex = r"{}\s*(TRUE|FALSE)".format(self.res_keyword)
        match = re.search(regex, rmsg)
        if match is None:
            return None
        else:
            res = match.group(1)
            if 'TRUE' in res:
                return True
            elif 'FALSE' in res:
                return False
            else:
                return None

    def gen_validate_file(self, input, pos, ranks):
        validate_dir = self.tmpdir / 'validate'
        if not validate_dir.exists():
            validate_dir.mkdir()
        validate_outf = validate_dir / (os.path.basename(input))
        validate_cmd = settings.CIL.RANK_VALIDATE(inf=input,
                                                  outf=validate_outf, 
                                                  pos=pos,
                                                  ranks=ranks)
        mlog.debug("validate_cmd: {}".format(validate_cmd))
        validate_rmsg, validate_errmsg = CM.vcmd(validate_cmd)
        # assert not trans_errmsg, "'{}': {}".format(trans_cmd, trans_errmsg)
        # mlog.debug("validate_rmsg: {}".format(validate_rmsg))
        # mlog.debug("validate_errmsg: {}".format(validate_errmsg))
        assert validate_outf.exists(), validate_outf
        return validate_outf

    def clean(self):
        cwd = os.path.dirname(__file__)
        items = os.listdir(cwd)

        for item in items:
            if item.endswith(".i") or item.endswith(".o"):
                os.remove(os.path.join(cwd, item))

class CPAchecker(Validator):
    def __init__(self, tmpdir):
        super().__init__(tmpdir)
        self.output_dir = self.tmpdir / settings.CPAchecker.CPA_OUTPUT_DIR

    @property
    def short_name(self):
        return settings.CPAchecker.CPA_SHORT_NAME

    @property
    def prove_reach_cmd(self):
        return partial(settings.CPAchecker.CPA_RUN, 
                       cpa_task_opts=settings.CPAchecker.CPA_REACH_OPTS)

    @property
    def validate_witness_cmd(self):
        return partial(settings.CPAchecker.CPA_RUN, 
                       cpa_task_opts=settings.CPAchecker.CPA_VALIDATE_OPTS(witness=self.witness))

    @property
    def witness_filename(self):
        return settings.CPAchecker.CPA_WITNESS_NAME

    @property
    def res_keyword(self):
        return settings.CPAchecker.CPA_RES_KEYWORD

    def mk_cex(self, vs):
        return CpaCex(vs)

    @property
    def cex_filename(self):
        return settings.CPAchecker.CPA_CEX_NAME

    @property
    def cex_smtlib_filename(self):
        return settings.CPAchecker.CPA_CEX_SMTLIB_NAME

class Ultimate(Validator):
    @property
    def prove_reach_cmd(self):
        return partial(settings.Ultimate.ULT_RUN, 
                       variant=self.name,
                       task=settings.Ultimate.ULT_REACH_TASK,
                       witness_dir=self.tmpdir,
                       witness_name=self.witness_filename)

    @property
    def validate_witness_cmd(self):
        return partial(settings.Ultimate.ULT_RUN, 
                       variant=self.name, 
                       task=settings.Ultimate.ULT_VALIDATE_TASK,
                       witness_dir=self.tmpdir,
                       witness_name=self.witness_filename)

    @property
    def witness_filename(self):
        return settings.Ultimate.ULT_WITNESS_NAME

    @property
    def res_keyword(self):
        return settings.Ultimate.ULT_RES_KEYWORD

    def mk_cex(self, vs):
        return UltCex(vs)

    @property
    def cex_filename(self):
        return settings.Ultimate.ULT_CEX_NAME

    @property
    def cex_smtlib_filename(self):
        return None

class UAutomizer(Ultimate):
    @property
    def short_name(self):
        return settings.Ultimate.UAUTOMIZER_SHORT_NAME

    @property
    def name(self):
        return settings.Ultimate.UAUTOMIZER_FULL_NAME

class UTaipan(Ultimate):
    @property
    def short_name(self):
        return settings.Ultimate.UTAIPAN_SHORT_NAME

    @property
    def name(self):
        return settings.Ultimate.UTAIPAN_FULL_NAME

class Portfolio(Validator):
    @property
    def short_name(self):
        return 'par'

    def prove_reach(self, vs, input):
        from utils.profiling import timeit

        # @timeit
        def f(task):
            vid, vld_cls = task
            vld = vld_cls(self.tmpdir)
            r, cex = vld.prove_reach(vs, input)
            if r is None:
                return None
            else:
                return vid, (r, cex)
        
        wrs = Miscs.run_mp_ex("prove_reach", 
                [(settings.CPAchecker.CPA_SHORT_NAME, CPAchecker), 
                 (settings.Ultimate.UAUTOMIZER_SHORT_NAME, UAutomizer),
                 (settings.Ultimate.UTAIPAN_SHORT_NAME, UTaipan)
                ], f, get_fst_res=True)
        mlog.debug('wrs: {}'.format(wrs))
        if wrs:
            vid, r = wrs[0]
            mlog.debug('Got result firstly from {}'.format(vid))
            return r
        else:
            return None, None

class Counterexample(object):
    def __init__(self, vs):
        self.vs = vs # inp_decls
        self.trans_cex = None
        self.symb_cex = None
        self.imap = None 

class CpaCex(Counterexample):
    def mk_trans_cex(self, cex_file):
        lines = [l.strip() for l in CM.iread(cex_file)]
        # regex = r"([_a-zA-Z0-9]+::)?([_a-zA-Z0-9]+)@(\d+): (\d+)"
        regex = r"(\w+::)?(\w+)@(\d+): (-?\d+)"
        ss = self.vs.names
        ss_len = len(ss)
        dcex = defaultdict(dict)
        is_interesting_local_var = lambda x: x in ss
        for l in lines:
            # mlog.debug(l)
            match = re.match(regex, l)
            if match:
                x = match.group(2)
                if is_interesting_local_var(x):
                    i = int(match.group(3))
                    v = int(match.group(4))
                    dcex[i][x] = v
        mlog.debug("dcex: {}".format(dcex))
        latest_i = None
        for i in sorted(dcex.keys(), reverse=True):
            if len(dcex[i]) == ss_len:
                j = i - 1
                if j in dcex and len(dcex[j]) == ss_len:
                    latest_i = i
        if latest_i:
            xs = tuple(dcex[latest_i][x] for x in ss)
            txs = tuple(dcex[latest_i - 1][x] for x in ss)
            t = data.traces.Trace.parse(ss, xs)
            tt = data.traces.Trace.parse(ss, txs)
            self.trans_cex = [(tt, t)]
        mlog.debug("trans_cex: {}".format(self.trans_cex))

    def mk_symb_cex(self, smtlib_file):
        vmap = self.mk_var_map_from_smtlib(smtlib_file)
        imap = self.mk_init_var_map(vmap)
        # mlog.debug('imap: {}'.format(imap))
        self.symb_cex = z3.parse_smt2_file(str(smtlib_file))
        self.imap = imap

    def mk_var_map_from_smtlib(self, smtlib_file):
        declare_fun_lines = [l.strip() for l in CM.iread(smtlib_file) if 'declare-fun' in l]
        regex = r"declare-fun \|?((?:\w+::)?(\w+)@(\d+))\|?" # (?:e) for non-grouping e
        vmap = defaultdict(dict)
        ss = self.vs.names
        for l in declare_fun_lines:
            match = re.search(regex, l)
            if match:
                v = match.group(2)
                if v in ss:
                    smt_var = match.group(1)
                    i = int(match.group(3))
                    vmap[v][i] = smt_var
        mlog.debug('vmap: {}'.format(vmap))
        return vmap

    def mk_init_var_map(self, vmap):
        imap = {}
        for v, m in vmap.items():
            init_i = min(m.keys())
            imap[v] = m[init_i]
        return imap

class UltCex(Counterexample):
    def mk_trans_cex(self, cex_file):
        # val_lines = [l for l in CM.iread(cex) if 'VAL' in l]
        # last_val_line = val_lines[-1]
        # mlog.debug("last_val_line: {}".format(last_val_line))
        # model_str = self._get_substring(last_val_line, '[', end_indicator=']')
        # model_parts = model_str.split(', ')
        # model = [part.strip().split('=') for part in model_parts]
        # dcex = dict((p[0], p[1]) for p in model)

        lines = CM.iread(cex_file)
        regex = r"VAL\s*\[(.*)\]"
        match = re.findall(regex, '\n'.join(lines))
        if match:
            model_str = match[-1]
            mregex = r"(\w+)=(-?\d+)"
            model = re.findall(mregex, model_str)
            dcex = dict(model)
            
            mlog.debug("dcex: {}".format(dcex))

            ss = self.vs.names
            tss = tuple('t' + s for s in ss)
            # mlog.debug("ss: {}".format(ss))
            # mlog.debug("tss: {}".format(tss))
            vs = tuple(dcex[s] for s in ss)
            t = data.traces.Trace.parse(ss, vs)
            tvs = tuple(dcex[ts] for ts in tss)
            tt = data.traces.Trace.parse(ss, tvs)
            self.trans_cex = [(tt, t)]
        mlog.debug("trans_cex: {}".format(self.trans_cex))

