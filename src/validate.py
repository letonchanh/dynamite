import os
from pathlib import Path
from functools import partial
import helpers.vcommon as CM
from utils import settings

mlog = CM.getLogger(__name__, settings.logger_level)

class Validator(object):
    def __init__(self):
        pass

    def prove_reach(self, input):
        assert input.is_file(), input
        cmd = self.prove_reach_cmd(input=input)
        mlog.debug("cmd: {}".format(cmd))
        rmsg, errmsg = CM.vcmd(cmd)
        assert not errmsg, "'{}': {}".format(cmd, errmsg)
        mlog.debug("rmsg: {}".format(rmsg))

class CPAchecker(Validator):
    @property
    def prove_reach_cmd(self):
        return partial(settings.CPAchecker.CPA_CMD, 
                       cpa_task_opts=settings.CPAchecker.CPA_REACH_OPTS)

    @property
    def validate_witness_cmd(self):
        return partial(settings.CPAchecker.CPA_CMD, 
                       cpa_task_opts=settings.CPAchecker.CPA_VALIDATE_OPTS)