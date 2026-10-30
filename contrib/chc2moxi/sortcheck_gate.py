#!/usr/bin/env python3
"""moxi-mc-flow's sort check, run as a gate.

    sortcheck_gate.py <file.moxi>        exit 0 == well sorted

This is the structural gate: it is what catches an invalid model -- primed
variables in `:inv` above all -- before it can reach the benchmark set and
quietly produce a wrong verdict.  It runs moxi-mc-flow's own `sort_check`
against moxi-mc-flow's own tables; the tool is imported, never modified.

`QF_ALIA`, arrays indexed by Int, now lives in moxi-mc-flow's own
`LOGIC_TABLE`, so this is a plain wrapper again.  The fallback below stays only
so the gate still works against an unpatched checkout; it is a no-op otherwise.
"""
import os
import pathlib
import sys

MMF = os.environ.get(
    "MOXI_MC_FLOW", os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, MMF)

from src import moxi, parse_moxi  # noqa: E402


def sort_check_apply_qf_alia(node) -> bool:
    identifier_class = (node.identifier.symbol, node.identifier.num_indices())
    if identifier_class in moxi.CORE_RANK_TABLE:
        return moxi.sort_check_apply_core(node)
    if identifier_class in moxi.ARRAY_RANK_TABLE:
        return moxi.sort_check_apply_arrays(node)
    if identifier_class in moxi.INT_RANK_TABLE:
        return moxi.sort_check_apply_int(node)
    return False


if "QF_ALIA" not in moxi.LOGIC_TABLE:
    moxi.LOGIC_TABLE["QF_ALIA"] = moxi.Logic(
        "QF_ALIA",
        {("Bool", 0), ("Int", 0), ("Array", 0)},
        moxi.CORE_RANK_TABLE.keys()
        | moxi.ARRAY_RANK_TABLE.keys()
        | moxi.INT_RANK_TABLE.keys(),
        sort_check_apply_qf_alia,
        False,
    )


def main(path: str) -> int:
    program = parse_moxi.parse(pathlib.Path(path))
    if not program:
        sys.stderr.write("failed parsing\n")
        return 1
    well_sorted, _ = moxi.sort_check(program)
    if not well_sorted:
        sys.stderr.write("failed sort check\n")
        return 1
    print("%s is well sorted" % path)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
