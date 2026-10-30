#!/usr/bin/env python3
"""moxi-mc-flow's MoXI -> MoXI-JSON step, with room to recurse.

    moxi2json_gate.py <in.moxi> <out.json>

`--with-lets` is mandatory for correctness (without it the frozen definitions
land in `:inv`, which MoXIchecker asserts at both the current and the next
state, silently turning REACHABLE into UNREACHABLE).  It also makes the term
tree as deep as the `let` chain is long, and both `Program.to_json()` and
`json.dump` walk that tree recursively.  The JSON is written compact: at
`indent=4` the indentation itself is proportional to the depth, so a deep
let-chain turns a 500 KB model into gigabytes of whitespace.  On the larger CHC-COMP models the walk
runs out of Python stack: `src/moxi2json.py` catches the first `RecursionError`
and retries at a limit of 20 000, which is still short for a chain of tens of
thousands of `let` bindings.

Raising `sys.setrecursionlimit` alone would segfault -- the limit is a counter,
the real constraint is the C stack -- so the work runs on a thread with a stack
big enough to hold the frames.  The tool itself is imported, never modified.
"""
import os
import pathlib
import sys
import threading

MMF = os.environ.get(
    "MOXI_MC_FLOW", os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, MMF)

from src import moxi2json  # noqa: E402

RECURSION_LIMIT = 300_000
STACK_BYTES = 512 * 1024 * 1024


def main() -> int:
    src, dst = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
    result = []

    def work():
        try:
            result.append(moxi2json.main(src, dst, False, False))
        except Exception as exc:                      # noqa: BLE001
            sys.stderr.write("%s: %s\n" % (type(exc).__name__, exc))
            result.append(1)

    sys.setrecursionlimit(RECURSION_LIMIT)
    threading.stack_size(STACK_BYTES)
    thread = threading.Thread(target=work)
    thread.start()
    thread.join()
    return result[0] if result else 1


if __name__ == "__main__":
    sys.exit(main())
