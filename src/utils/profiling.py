import time
import logging
import helpers.vcommon as CM
from utils import settings
from collections import defaultdict
import inspect

mlog = CM.getLogger(__name__, settings.logger_level)

time_log = defaultdict(float)

def get_class_of_method(method):
    for cls in inspect.getmro(method.im_class):
        if method.__name__ in cls.__dict__: 
            return cls
    return None

def timeit(method):
    if settings.logger_level == logging.DEBUG:
        def timed(*args, **kw):
            # start_time = timeit.default_timer()
            start_time = time.time()
            result = method(*args, **kw)
            # elapsed = timeit.default_timer() - start_time
            elapsed = time.time() - start_time
            time_log[method.__name__] += elapsed * 1000
            if 'log_time' in kw:
                name = kw.get('log_name', method.__name__)
                kw['log_time'][name] = elapsed * 1000
            else:
                mlog.debug("{}: {:.2f}ms".format(method.__name__, elapsed * 1000))
            return result
        return timed
    else:
        return method