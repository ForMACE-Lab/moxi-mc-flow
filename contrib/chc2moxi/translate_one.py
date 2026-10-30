#!/usr/bin/env python3
"""Translate one CHC-COMP benchmark into MoXI.

    translate_one.py <src.smt2[.gz]> <task-name> <outdir>

Writes <outdir>/<logic>/<task-name>.moxi (and .json, if moxi2json finishes)
on success and prints one CSV row on stdout:

    task,status,logic,seconds,src

status is one of ok / ok-nojson / ok-unsupported-logic / nonlinear /
read-fail / horn2vmt-fail / horn2vmt-timeout / vmt2moxi-fail /
vmt2moxi-timeout / sortcheck-fail / sortcheck-timeout / empty.

Environment: HORN2VMT is the horn2vmt binary (default: horn2vmt on the PATH),
MOXI_MC_FLOW the moxi-mc-flow checkout to use (default: this repository).
"""
import gzip
import os
import re
import subprocess
import sys
import tempfile
import time

# horn2vmt from ic3ia, and the moxi-mc-flow checkout whose translate.py and
# src/ are used (by default the one this script lives in).
HORN2VMT = os.environ.get("HORN2VMT", "horn2vmt")
MOXI_MC_FLOW = os.environ.get(
    "MOXI_MC_FLOW", os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
TRANSLATE = os.path.join(MOXI_MC_FLOW, "translate.py")
SORTCHECK = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sortcheck_gate.py")
MOXI2JSON = os.path.join(os.path.dirname(os.path.abspath(__file__)), "moxi2json_gate.py")

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sanitize_vmt import sanitize, restore_int_div
from presanitize_chc import presanitize, normalize_heads

H2V_TIMEOUT = int(os.environ.get("H2V_TIMEOUT", 120))
V2M_TIMEOUT = int(os.environ.get("V2M_TIMEOUT", 300))
# The MoXI -> MoXI-JSON step is the slowest and the most load-sensitive of the
# gates, so it gets its own budget: under heavy parallelism a large model can
# miss a 300 s deadline it clears comfortably on its own, and the CHC-COMP set
# keeps only the .moxi, so losing a file here costs a benchmark entry for a
# reason that has nothing to do with the model.
JSON_TIMEOUT = int(os.environ.get("JSON_TIMEOUT", V2M_TIMEOUT))

# MoXIchecker's SUPPORTED_LOGIC, unpatched
# (moxichecker/encoding/moxi2smt.py: BV_LOGIC | INT_LOGIC | REAL_LOGIC).
SUPPORTED = {"QF_BV", "QF_ABV", "QF_LIA", "QF_NIA", "QF_ALIA", "QF_AUFLIA",
             "QF_LRA", "QF_NRA"}

# Both sort checkers cut operators out of the *linear* fragments: QF_LIA drops
# `/`, `div`, `mod` and `abs`, and QF_LRA takes `(* c x)` only for a literal c.
# A file that needs one of those is not wrong, it is just not linear in the
# SMT-LIB sense, so the label widens by one step rather than the file being
# dropped.  Widening only ever goes to a superset logic, so a model that passes
# under the wider label means the same thing.
LOGIC_LADDER = {
    "QF_LIA": ["QF_LIA", "QF_NIA"],
    "QF_LRA": ["QF_LRA", "QF_NRA"],
}


def read_source(path):
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt", errors="replace") as fh:
        return fh.read()


def infer_logic(text):
    """The narrowest MoXIchecker logic that covers the sorts and operators used."""
    has_array = "(Array " in text
    has_bv = "(_ BitVec" in text
    has_real = re.search(r"\bReal\b", text) is not None
    has_int = re.search(r"\bInt\b", text) is not None
    # A '*' whose two arguments are both non-numeric makes the arithmetic
    # nonlinear; MathSAT emits the linear case as (* (- 1) x) or (* 2 x).
    nonlinear = re.search(r"\(\*\s+(?!\(-\s*\d|\d)[^\s()]+\s+(?!\(-\s*\d|\d)[^\s()]+", text) is not None
    if has_bv:
        return "QF_ABV" if has_array else "QF_BV"
    if has_array:
        # Arrays indexed by Int.  MoXIchecker lists QF_ALIA in SUPPORTED_LOGIC
        # and maps select/store/const onto pySMT, and moxi-mc-flow's
        # LOGIC_TABLE now carries the matching sort-check entry.
        return "QF_ALIA"
    if has_int and has_real:
        # MathSAT rewrites `mod` and `div` through Real arithmetic, so an
        # all-integer source can come back with a stray Real.  restore_int_div
        # undoes that where the divisor is a positive numeral; what is left
        # here is genuinely mixed, and naming it QF_LRA or QF_LIA would be a
        # lie that also breaks numeral parsing in the encoder.
        return "QF_LIRA"          # not in SUPPORTED; reported, not run
    # QF_LIA's sort check drops `/`, `div`, `mod` and `abs`, so a model that
    # kept one after the div/mod restoration starts at QF_NIA rather than
    # paying for a QF_LIA check that cannot pass.
    int_div = re.search(r"\((?:div|mod|abs) ", text) is not None
    if has_real:
        return "QF_NRA" if nonlinear else "QF_LRA"
    if has_int:
        return "QF_NIA" if (nonlinear or int_div) else "QF_LIA"
    return "QF_LIA"


def main():
    src, task, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
    t0 = time.time()

    def done(status, logic=""):
        print("%s,%s,%s,%.1f,%s" % (task, status, logic, time.time() - t0, src))
        sys.exit(0)

    try:
        chc = read_source(src)
    except Exception:
        done("read-fail")

    tmp = tempfile.mkdtemp(prefix="chc2moxi-")
    vmt_path = os.path.join(tmp, "x.vmt")
    moxi_path = os.path.join(tmp, "x.moxi")
    json_path = os.path.join(tmp, "x.json")
    try:
        try:
            chc, _ = presanitize(chc)
        except Exception:
            pass                      # a file we cannot even tokenise goes on
                                      # to horn2vmt unchanged and fails there
        def horn2vmt(text):
            try:
                return subprocess.run([HORN2VMT], input=text, capture_output=True,
                                      text=True, timeout=H2V_TIMEOUT)
            except subprocess.TimeoutExpired:
                done("horn2vmt-timeout")

        p = horn2vmt(chc)
        if p.returncode != 0 or not p.stdout.strip():
            err = (p.stderr or "")[:200]
            if "non-unary" in err:
                done("nonlinear")
            # A clause head carrying a literal instead of a variable makes
            # horn2vmt read past the end of its argument list and die on a
            # signal.  Normalising the heads costs one fresh variable per
            # offending argument and leaves the models untouched, so it is
            # worth one retry before giving up on the file.
            try:
                retry, hn = normalize_heads(chc)
            except Exception:
                hn = None
            if hn and hn.get("head-normalised"):
                p = horn2vmt(retry)
            if p.returncode != 0 or not p.stdout.strip():
                err = (p.stderr or "")[:200]
                done("nonlinear" if "non-unary" in err else "horn2vmt-fail")

        clean, _ = sanitize(p.stdout)
        clean, _ = restore_int_div(clean)
        with open(vmt_path, "w") as fh:
            fh.write(clean)

        try:
            q = subprocess.run([sys.executable, TRANSLATE, vmt_path, "moxi",
                                "--with-lets",
                                "--output", moxi_path, "--overwrite"],
                               capture_output=True, text=True, timeout=V2M_TIMEOUT)
        except subprocess.TimeoutExpired:
            done("vmt2moxi-timeout")
        if q.returncode != 0 or not os.path.exists(moxi_path):
            done("vmt2moxi-fail")

        with open(moxi_path) as fh:
            moxi = fh.read()
        if ":reachable" not in moxi:
            done("empty")

        guess = infer_logic(moxi)

        # Gate on moxi-mc-flow's own sort checker.  It is what catches a
        # structurally invalid model -- primed variables in :inv above all --
        # before it can reach the benchmark set and quietly produce wrong
        # verdicts.  A model that does not pass is not placed.
        logic = guess
        for candidate in LOGIC_LADDER.get(guess, [guess]):
            text = re.sub(r"^\(set-logic [^)]*\)", "(set-logic %s)" % candidate,
                          moxi, count=1)
            with open(moxi_path, "w") as fh:
                fh.write(text)
            try:
                v = subprocess.run([sys.executable, SORTCHECK, moxi_path],
                                   capture_output=True, text=True,
                                   timeout=V2M_TIMEOUT)
            except subprocess.TimeoutExpired:
                done("sortcheck-timeout", candidate)
            logic = candidate
            if v.returncode == 0 and "is well sorted" in (v.stdout + v.stderr):
                break
        else:
            done("sortcheck-fail", logic)

        # The JSON rendering is a convenience artifact, not part of the model:
        # the CHC-COMP benchmark stores only .moxi for these tasks, and the
        # sort checker above has already accepted the model.  moxi2json is
        # superlinear in `let` depth, so on the deepest models it runs out of
        # budget while the .moxi beside it is perfectly good.  Losing the JSON
        # therefore downgrades the result, it does not reject it.
        have_json = False
        try:
            r = subprocess.run([sys.executable, MOXI2JSON, moxi_path, json_path],
                               capture_output=True, text=True, timeout=JSON_TIMEOUT)
            have_json = r.returncode == 0 and os.path.exists(json_path)
        except subprocess.TimeoutExpired:
            have_json = False

        dest = os.path.join(outdir, logic)
        os.makedirs(dest, exist_ok=True)
        os.replace(moxi_path, os.path.join(dest, task + ".moxi"))
        if have_json:
            os.replace(json_path, os.path.join(dest, task + ".json"))
        if logic not in SUPPORTED:
            done("ok-unsupported-logic", logic)
        done("ok" if have_json else "ok-nojson", logic)
    finally:
        subprocess.run(["rm", "-rf", tmp])


if __name__ == "__main__":
    main()
