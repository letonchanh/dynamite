import os
import re
import traceback
import shutil
from pathlib import Path
from functools import partial
import helpers.vcommon as CM
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
        self.witness = self.tmpdir / self.witness_filename
        self.output_dir = None

    def prove_reach(self, vs, input):
        cwd = os.getcwd()
        trans_cex = None
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
                assert self.witness.is_file(), self.witness
                vcmd = self.validate_witness_cmd(input=input)
                mlog.debug("vcmd: {}".format(vcmd))
                v_rmsg, v_errmsg = CM.vcmd(vcmd)
                # assert not v_errmsg, "'{}': {}".format(vcmd, v_errmsg)
                mlog.debug("v_rmsg: {}".format(v_rmsg))
                # mlog.debug("v_errmsg: {}".format(v_errmsg))
                v_res = self.parse_rmsg(v_rmsg)
                assert v_res is False, v_res
                cex_file = self.tmpdir / self.cex_filename
                assert cex_file.is_file(), cex_file
                trans_cex = self.parse_trans_cex(vs, cex_file)

        except Exception as ex:
            mlog.debug("Exception: {}".format(ex))
            mlog.debug(traceback.format_exc())
            res = None
        finally:
            os.chdir(cwd)
            return res, trans_cex

    def _get_substring(self, s, start_indicator, end_indicator=None):
        start_index = s.find(start_indicator)
        if start_index != -1:
            if end_indicator:
                end_index = s.find(end_indicator)
                if end_index != -1:
                    return s[(start_index + len(start_indicator)):end_index]
                else:
                    return s[(start_index + len(start_indicator)):]
            else:
                return s[(start_index + len(start_indicator)):]
        else:
            return None

    def parse_rmsg(self, rmsg):
        res = self._get_substring(rmsg, self.res_keyword)
        mlog.debug("res: {}".format(res))
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

    @property
    def cex_filename(self):
        return settings.CPAchecker.CPA_CEX_NAME

    def parse_trans_cex(self, vs, cex):
        lines = [l.strip() for l in CM.iread(cex)]
        regex = r"([_a-zA-Z0-9]+::)?([_a-zA-Z0-9]+)@(\d+): (\d+)"
        ss = vs.names
        ss_len = len(ss)
        dcex = defaultdict(dict)
        is_interesting_local_var = lambda x: x in ss
        for l in lines:
            mlog.debug(l)
            match = re.match(regex, l)
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
            trans_cex = (tt, t)
            mlog.debug("trans_cex: {}".format(trans_cex))
            return [trans_cex]
        return []

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

    @property
    def cex_filename(self):
        return settings.Ultimate.ULT_CEX_NAME

    def parse_trans_cex(self, vs, cex):
        val_lines = [l for l in CM.iread(cex) if 'VAL' in l]
        last_val_line = val_lines[-1]
        mlog.debug("last_val_line: {}".format(last_val_line))
        model_str = self._get_substring(last_val_line, '[', end_indicator=']')
        model_parts = model_str.split(', ')
        model = [part.strip().split('=') for part in model_parts]
        dcex = dict((p[0], p[1]) for p in model)
        mlog.debug("dcex: {}".format(dcex))

        ss = vs.names
        tss = tuple('t' + s for s in ss)
        # mlog.debug("ss: {}".format(ss))
        # mlog.debug("tss: {}".format(tss))
        vs = tuple(dcex[s] for s in ss)
        t = data.traces.Trace.parse(ss, vs)
        tvs = tuple(dcex[ts] for ts in tss)
        tt = data.traces.Trace.parse(ss, tvs)
        trans_cex = (tt, t)
        mlog.debug("trans_cex: {}".format(trans_cex))
        return [trans_cex]

class UAutomizer(Ultimate):
    @property
    def short_name(self):
        return settings.Ultimate.UAUTOMIZER_SHORT_NAME

    @property
    def name(self):
        return settings.Ultimate.UAUTOMIZER_FULL_NAME
        