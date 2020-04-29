import time
import logging
import helpers.vcommon as CM
from utils import settings

mlog = CM.getLogger(__name__, settings.logger_level)

def timeit(method):
    if settings.logger_level == logging.DEBUG:
        def timed(*args, **kw):
            # start_time = timeit.default_timer()
            start_time = time.time()
            result = method(*args, **kw)
            # elapsed = timeit.default_timer() - start_time
            elapsed = time.time() - start_time
            if 'log_time' in kw:
                name = kw.get('log_name', method.__name__)
                kw['log_time'][name] = int(elapsed * 1000)
            else:
                mlog.debug("{}: {:.2f}ms".format(method.__name__, elapsed * 1000))
            return result
        return timed
    else:
        return method