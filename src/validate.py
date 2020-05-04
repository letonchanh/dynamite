import os
import traceback
from pathlib import Path
from functools import partial
import helpers.vcommon as CM
from utils import settings

mlog = CM.getLogger(__name__, settings.logger_level)

class Validator(object):
    def __init__(self, tmpdir):
        mytempdir = tmpdir / self.short_name
        if not mytempdir.exists():
            mytempdir.mkdir()
        self.tmpdir = mytempdir
        self.witness_name = 'witness.graphml'

    def prove_reach(self, input):
        cwd = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            assert input.is_file(), input
            cmd = self.prove_reach_cmd(input=input)
            mlog.debug("cmd: {}".format(cmd))
            rmsg, errmsg = CM.vcmd(cmd)
            assert not errmsg, "'{}': {}".format(cmd, errmsg)
            # mlog.debug("rmsg: {}".format(rmsg))
            res = self.parse_rmsg(rmsg)
            mlog.debug("res: {}".format(res))
        except Exception as ex:
            mlog.debug("Exception: {}".format(ex))
            mlog.debug(traceback.format_exc())
            res = None
        finally:
            os.chdir(cwd)
            return res

class CPAchecker(Validator):
    @property
    def short_name(self):
        return "cpa"

    @property
    def prove_reach_cmd(self):
        return partial(settings.CPAchecker.CPA_CMD, 
                       cpa_task_opts=settings.CPAchecker.CPA_REACH_OPTS)

    @property
    def validate_witness_cmd(self):
        return partial(settings.CPAchecker.CPA_CMD, 
                       cpa_task_opts=settings.CPAchecker.CPA_VALIDATE_OPTS(witness=self.witness))

class UAutomizer(Validator):
    @property
    def short_name(self):
        return "ult"

    @property
    def prove_reach_cmd(self):
        return partial(settings.Ultimate.ULT_CMD, 
                       variant="UAutomizer", 
                       witness_dir=self.tmpdir,
                       witness_name=self.witness_name)

    def parse_rmsg(self, rmsg):
        res_keyword = 'Result:'
        res_index = rmsg.find(res_keyword)
        if res_index != -1:
            res = rmsg[(res_index + len(res_keyword)):]
            if 'TRUE' in res:
                return True
            elif 'FALSE' in res:
                return False
            else:
                return None
        else:
            return None