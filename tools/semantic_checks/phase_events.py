"""Optional phase observations; events never affect the relation or solver plan."""
from contextlib import contextmanager
import time


@contextmanager
def timed_phase(callback, name):
    if callback is None:
        yield
        return
    started = time.perf_counter()
    callback(dict(phase=name, event='started', observed_unix=time.time()))
    try:
        yield
    except BaseException:
        callback(dict(phase=name, event='failed', observed_unix=time.time(),
                      elapsed_seconds=time.perf_counter()-started))
        raise
    else:
        callback(dict(phase=name, event='completed', observed_unix=time.time(),
                      elapsed_seconds=time.perf_counter()-started))
