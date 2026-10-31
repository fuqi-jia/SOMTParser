"""Run long pytest node selections without OS argv limits; spawn-safe entry."""
import json
from pathlib import Path
import sys
import time


def main():
    import pytest

    arguments = json.loads(Path(sys.argv[1]).read_text())
    if not isinstance(arguments, list) or not all(isinstance(arg, str) for arg in arguments):
        raise ValueError('pytest argument file must contain a JSON string array')
    started = time.time()
    code = pytest.main(arguments)
    result = dict(pytest_returncode=int(code), started=started, finished=time.time())
    output = Path(sys.argv[2])
    temporary = output.with_suffix(output.suffix + '.partial')
    temporary.write_text(json.dumps(result, indent=2) + '\n')
    temporary.replace(output)
    return int(code)


# multiprocessing.spawn imports this file as __mp_main__ before invoking the
# requested child target. It must never recursively re-enter pytest there.
if __name__ == '__main__':
    raise SystemExit(main())
