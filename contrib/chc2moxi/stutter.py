#!/usr/bin/env python3
"""Make a CHC-COMP-derived MoXI task deadlock-free with a stuttering step.

    stutter.py FILE.moxi ...      (rewrites the files in place)

It writes the same formula as the --add-stutter option of the VMT-to-MoXI
translation (ForMACE-Lab/moxi-mc-flow, branch vmt2moxi-stutter, 5a00f91), but
on the already translated file:

    :trans T   ==>   :trans (or T (and (= v1' v1) ... (= vn' vn)))

over the state variables v1..vn, which in these tasks are exactly the
:output variables (:input and :local are empty, checked below).  Only the
:trans term changes; every other byte of the file stays the same.
"""
import re, sys
from pathlib import Path

SYM = r"\|[^|]*\||[^\s()|]+"

def skip_term(t, i):
    """index just past the term that starts at t[i]"""
    if t[i] == "|":
        return t.index("|", i + 1) + 1
    if t[i] != "(":
        j = i
        while j < len(t) and not t[j].isspace() and t[j] not in "()":
            j += 1
        return j
    d = 0; j = i
    while j < len(t):
        c = t[j]
        if c == "|":
            j = t.index("|", j + 1)
        elif c == "(":
            d += 1
        elif c == ")":
            d -= 1
            if d == 0:
                return j + 1
        j += 1
    raise ValueError("unbalanced term")

def attr_span(t, name, start=0):
    m = re.compile(r":%s\s+" % name).search(t, start)
    if not m:
        raise ValueError(f"no :{name}")
    return m.end(), skip_term(t, m.end())

def stutter(t):
    ds = t.index("(define-system")
    for empty in ("input", "local"):
        a, b = attr_span(t, empty, ds)
        if t[a:b].strip() != "()":
            raise ValueError(f":{empty} is not empty")
    a, b = attr_span(t, "output", ds)
    outs = re.findall(r"\((%s)\s+(?:\([^()]*\)|[^()\s]+)\)" % SYM, t[a:b])
    # as moxi.conjoin_list: no variables -> true, one -> the equation, more -> and
    eqs = " ".join(f"(= {v}' {v})" for v in outs)
    keep = "true" if not outs else eqs if len(outs) == 1 else f"(and {eqs})"
    a, b = attr_span(t, "trans", ds)
    return t[:a] + f"(or {t[a:b]} {keep})" + t[b:]

if __name__ == "__main__":
    for f in sys.argv[1:]:
        p = Path(f)
        p.write_text(stutter(p.read_text()))
