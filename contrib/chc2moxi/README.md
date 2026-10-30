# CHC-COMP to MoXI

The scripts that translated the CHC-COMP 2025 benchmarks into the MoXI tasks
of SV-Benchmarks (`moxi/*/chc-comp25/`, merge request !1797 of
sosy-lab/benchmarking/sv-benchmarks).

## Steps

`translate_one.py` translates one clause file. For each file it runs:

1. `presanitize_chc.py`: rewrites the constructs that MathSAT, and so
   `horn2vmt`, does not parse (n-ary `concat`; Z3's `bvudiv_i` and its
   siblings, only for a non-zero literal divisor; `rem`, only for a positive
   literal divisor; symbols delimited by backslashes). If `horn2vmt` then fails, it retries once with clause
   heads that carry a variable instead of a literal (`normalize_heads`).
2. `horn2vmt` (from ic3ia): CHC to VMT-LIB. It rejects non-linear clauses.
3. `sanitize_vmt.py`: renames pipe-quoted symbols that the MoXI lexer
   cannot read, turns MathSAT's encoding of integer `div` and `mod` back
   into `div` and `mod` (only for a positive literal divisor), drops sort
   ascriptions on nullary symbols, and writes rational constants as
   decimals.
4. `translate.py <file>.vmt moxi --with-lets` of moxi-mc-flow: VMT-LIB to
   MoXI.
5. The logic: `translate.py` writes `(set-logic ALL)`, so the narrowest
   logic is inferred from the model, and `sortcheck_gate.py` (moxi-mc-flow's
   sort checker) must accept the model under it. `QF_LIA` and `QF_LRA` widen
   one step to `QF_NIA` and `QF_NRA` if the sort check needs it. A model
   that no logic accepts is dropped.
6. `moxi2json_gate.py`: MoXI-JSON, with a large stack for deep `let`
   chains. Only the `.moxi` files went into SV-Benchmarks.

After that, `stutter.py` adds a stuttering step to each task, so that no
state is a deadlock:

    :trans T   ==>   :trans (or T (and (= v1' v1) ... (= vn' vn)))

over the state variables. This is the same formula as the `--add-stutter`
option of the branch `vmt2moxi-stutter` (5a00f91), applied to the translated
files instead of during the translation.

## Versions used

- CHC-COMP benchmarks: https://github.com/chc-comp/chc-comp25-benchmarks,
  commit ddd279cab0717db6effe69baad451a8eb04ffd86.
- horn2vmt: ic3ia from https://es-static.fbk.eu/people/griggio/ic3ia/,
  downloaded on Aug 28, 2026 (then the unversioned `ic3ia.tar.gz`), built
  with MathSAT 5.6.10. Its `horn2vmt.cpp` and `ts.h` are identical to those
  in `ic3ia-26.10.tar.gz`.
- moxi-mc-flow (`translate.py` and `src/`): commit
  bd3c6086b817c2ebbddd10ea51c0fb37bd1a76eb of this branch.

## Usage

    export HORN2VMT=/path/to/ic3ia/build/horn2vmt
    export MOXI_MC_FLOW=/path/to/moxi-mc-flow    # a checkout of bd3c608
    python3 translate_one.py chc.smt2 chc25-lialin-0000 out/
    python3 stutter.py out/QF_LIA/chc25-lialin-0000.moxi

`MOXI_MC_FLOW` defaults to this repository. `contrib/setup-ic3ia.sh` builds
horn2vmt from an ic3ia source tree.

## Check

On a sample of 45 tasks (15 each of QF_LIA, QF_BV and QF_LRA), these
scripts with bd3c608 give byte-identical `.moxi` files to the ones of the
original translation run. With `stutter.py`, they give exactly the models in
SV-Benchmarks, apart from the comment header added there. The head of this
branch also gives the same files on this sample.
