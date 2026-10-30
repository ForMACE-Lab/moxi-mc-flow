#!/usr/bin/env python3
"""Rewrite MathSAT's VMT output into the fragment moxi-mc-flow can carry.

Three separate jobs, all of them on the VMT that `horn2vmt` just printed and
none of them on either tool:

1. Pipe-quoted symbols.  MathSAT keeps the identifiers of the source CHC file,
   which routinely contain characters SMT-LIB does not allow in a simple symbol
   -- ':' above all (`|$knormal:3|`).  moxi-mc-flow prints such a symbol
   unquoted in some positions and the MoXI lexer then reads `:3` as a keyword.
   A symbol that is already simple is left alone; otherwise it becomes
   `v<n>__<slug>`, which keeps a readable trace of the original name.

2. Integer division and modulo.  MathSAT has no Int division in its term
   language, so the parser rewrites `(div x k)` into the mixed-arithmetic term
   `(to_int (* (/ 1 k) (to_real x)))` and `(mod x k)` into
   `x + (-k) * (to_int (* (/ 1 k) (to_real x)))`.  Both are faithful -- `to_int`
   is floor, and Euclidean and floor division agree for a positive divisor --
   but MoXI has no mixed Int/Real logic, so the file fails the sort check and
   is dropped.  `restore_int_div` runs the rewrite backwards, recovering `div`
   and `mod`, which QF_NIA has.  It fires only for a **positive numeral**
   divisor, where floor and Euclidean division are the same function; any other
   shape is left as it stands and the file still fails, which is the
   conservative outcome.

3. Sort ascriptions.  `(as x Int)` on a declared nullary symbol says nothing
   the declaration does not, and moxi-mc-flow's VMT grammar accepts a qualified
   identifier only in the head of an application, not as a term.  The
   ascription is dropped.  `(as const (Array Int Int))`, where it does carry
   the sort, has a compound sort and is left alone.

4. Rational constants.  MathSAT writes a Real coefficient as `(/ p q)` and a
   Real literal as `(to_real 0)` / `(to_real (- 1))`.  moxi-mc-flow's QF_LRA
   check accepts `(* c x)` only for a *literal* c, and neither it nor
   MoXIchecker knows `to_real` (MoXIchecker's handler calls FNode.to_real(),
   which pySMT does not have).  Both are folded into a plain decimal, which is
   the same number written the way both tools read.  A rational that has no
   finite decimal form is left alone.
"""
import math
import re
import sys
from fractions import Fraction

SIMPLE = re.compile(r"^[A-Za-z~!@$%^&*_+=<>.?/-][A-Za-z0-9~!@$%^&*_+=<>.?/-]*$")
QUOTED = re.compile(r"\|([^|]*)\|")

TO_REAL_NEG = re.compile(r"\(to_real \(- (\d+)\)\)")
TO_REAL_POS = re.compile(r"\(to_real (\d+)\)")

# (define-fun NAME () SORT BODY) -- MathSAT prints one command per line.
DEFINE = re.compile(r"^\(define-fun (\S+) \(\) (\S+) (.*)\)\s*$")

# The two shapes the int-division rewrite leaves behind.
RATIO = re.compile(r"^\(\* \(/ 1 (\d+)\) \(to_real (\S+)\)\)$")
TO_INT = re.compile(r"^\(to_int (\S+)\)$")
TO_INT_INLINE = re.compile(r"^\(to_int \(\* \(/ 1 (\d+)\) \(to_real (\S+)\)\)\)$")
NEG_PROD = re.compile(r"^\(\* \(- (\d+)\) (\S+)\)$")
SUM = re.compile(r"^\(\+ (\S+) (\S+)\)$")

# A rational constant, as MathSAT prints one.
RAT = re.compile(r"\(/ (\d+) (\d+)\)")

# A sort ascription on a nullary symbol, `(as x Int)`.  MathSAT prints it when
# the source declared the symbol with an ambiguous name; it carries no
# information a declared symbol does not already have, and moxi-mc-flow's VMT
# grammar has no production for a qualified identifier in term position.  The
# sort must be a single token, so `(as const (Array Int Int))` -- where the
# ascription *is* load-bearing -- does not match and is left alone.
AS_ASCRIPTION = re.compile(r"\(as (\|[^|]*\||[^\s()|]+) ([^\s()]+)\)")


def _decimal(num, den):
    """`num/den` as a finite SMT-LIB decimal, or None when it has none."""
    f = Fraction(num, den)
    d = f.denominator
    for p in (2, 5):
        while d % p == 0:
            d //= p
    if d != 1:
        return None
    s = str(f.numerator / f.denominator) if f.denominator else None
    # Build it exactly rather than through float.
    digits = 0
    d = f.denominator
    while d % 2 == 0:
        d //= 2
        digits += 1
    d, five = f.denominator, 0
    while d % 5 == 0:
        d //= 5
        five += 1
    digits = max(digits, five)
    scaled = f.numerator * (10 ** digits) // f.denominator
    s = str(abs(scaled)).rjust(digits + 1, "0")
    s = (s[:len(s) - digits] + "." + s[len(s) - digits:]) if digits else s + ".0"
    return ("-" + s) if f.numerator < 0 else s


def sanitize(text):
    mapping = {}
    counter = [0]

    def safe(name):
        if name in mapping:
            return mapping[name]
        if SIMPLE.match(name):
            new = name
        else:
            slug = re.sub(r"[^A-Za-z0-9_]", "_", name).strip("_") or "sym"
            new = "v%d__%s" % (counter[0], slug[:40])
            counter[0] += 1
        mapping[name] = new
        return new

    out = []
    for line in text.splitlines(True):
        if line.lstrip().startswith("(set-info"):
            continue
        line = AS_ASCRIPTION.sub(lambda m: m.group(1), line)
        line = TO_REAL_NEG.sub(lambda m: "(- %s.0)" % m.group(1), line)
        line = TO_REAL_POS.sub(lambda m: "%s.0" % m.group(1), line)
        out.append(QUOTED.sub(lambda m: safe(m.group(1)), line))
    return "".join(out), mapping


def _sexp(text):
    """Parse one term into nested lists of tokens."""
    toks, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c in "()":
            toks.append(c); i += 1
        elif c in " \t\r\n":
            i += 1
        elif c == "|":
            j = text.find("|", i + 1); j = n - 1 if j < 0 else j
            toks.append(text[i:j + 1]); i = j + 1
        else:
            j = i
            while j < n and text[j] not in "()| \t\r\n":
                j += 1
            toks.append(text[i:j]); i = j
    stack, cur = [], []
    for t in toks:
        if t == "(":
            stack.append(cur); cur = []
        elif t == ")":
            if not stack:
                continue
            done, cur = cur, stack.pop(); cur.append(done)
        else:
            cur.append(t)
    while stack:
        done, cur = cur, stack.pop(); cur.append(done)
    return cur[0] if len(cur) == 1 else cur


def _print(node):
    if isinstance(node, list):
        return "(" + " ".join(_print(c) for c in node) + ")"
    return node


NUM = re.compile(r"^\d+$")
DEC = re.compile(r"^\d+\.\d+$")


def _const(node):
    """The rational a literal denotes, or None."""
    if isinstance(node, str):
        if NUM.match(node) or DEC.match(node):
            return Fraction(node)
        return None
    if isinstance(node, list) and len(node) == 2 and node[0] == "-":
        inner = _const(node[1])
        return None if inner is None else -inner
    if isinstance(node, list) and len(node) == 3 and node[0] == "/":
        a, b = _const(node[1]), _const(node[2])
        if a is None or b is None or b == 0:
            return None
        return a / b
    return None


def _linear(node, defs, memo, depth=0):
    """The Real term as a linear form over `to_real` atoms.

    Returns {atom-text: Fraction} with the constant under the key None, or None
    when the term is not a rational-linear combination of integers.  MathSAT
    only ever produces that shape when it eliminates Int division, which is the
    single reason a Real term appears in an otherwise integer system.
    """
    if depth > 200:
        return None
    c = _const(node)
    if c is not None:
        return {None: c}
    if isinstance(node, str):
        if node in memo:
            return memo[node]
        if node in defs and defs[node][0] == "Real":
            memo[node] = None                      # break cycles
            form = _linear(_sexp(defs[node][1]), defs, memo, depth + 1)
            memo[node] = form
            return form
        return None
    if not isinstance(node, list) or not node:
        return None
    head = node[0]
    if head == "to_real" and len(node) == 2:
        return {_print(node[1]): Fraction(1)}
    if head == "+":
        acc = {None: Fraction(0)}
        for arg in node[1:]:
            f = _linear(arg, defs, memo, depth + 1)
            if f is None:
                return None
            for k, v in f.items():
                acc[k] = acc.get(k, Fraction(0)) + v
        return acc
    if head == "-" and len(node) == 2:
        f = _linear(node[1], defs, memo, depth + 1)
        return None if f is None else {k: -v for k, v in f.items()}
    if head == "-" and len(node) > 2:
        acc = _linear(node[1], defs, memo, depth + 1)
        if acc is None:
            return None
        acc = dict(acc)
        for arg in node[2:]:
            f = _linear(arg, defs, memo, depth + 1)
            if f is None:
                return None
            for k, v in f.items():
                acc[k] = acc.get(k, Fraction(0)) - v
        return acc
    if head == "*" and len(node) == 3:
        for a, b in ((node[1], node[2]), (node[2], node[1])):
            k = _const(a)
            if k is not None:
                f = _linear(b, defs, memo, depth + 1)
                if f is None:
                    return None
                return {kk: vv * k for kk, vv in f.items()}
        return None
    if head == "/" and len(node) == 3:
        k = _const(node[2])
        if k is None or k == 0:
            return None
        f = _linear(node[1], defs, memo, depth + 1)
        return None if f is None else {kk: vv / k for kk, vv in f.items()}
    return None


def _as_int_div(form):
    """`floor(form)` written with Int `div`, or None.

    Every coefficient is put over one positive denominator d, so the term is
    floor(N/d) for an integer expression N.  SMT-LIB `div` is Euclidean, which
    coincides with floor exactly when the divisor is positive -- hence the
    normalisation to d > 0 rather than a guess at the sign.
    """
    if form is None:
        return None
    den = 1
    for v in form.values():
        den = den * v.denominator // math.gcd(den, v.denominator)
    if den <= 0:
        return None
    terms = []
    for atom, coeff in form.items():
        if atom is None:
            continue
        c = coeff * den
        if c.denominator != 1:
            return None
        c = c.numerator
        if c == 0:
            continue
        if c == 1:
            terms.append(atom)
        elif c < 0:
            terms.append("(* (- %d) %s)" % (-c, atom))
        else:
            terms.append("(* %d %s)" % (c, atom))
    const = form.get(None, Fraction(0)) * den
    if const.denominator != 1:
        return None
    const = const.numerator
    if const:
        terms.append(("(- %d)" % -const) if const < 0 else str(const))
    if not terms:
        num = "0"
    elif len(terms) == 1:
        num = terms[0]
    else:
        num = terms[0]
        for t in terms[1:]:
            num = "(+ %s %s)" % (num, t)
    return num if den == 1 else "(div %s %d)" % (num, den)


REAL_OPS = {"+", "-", "*"}


def _realify(node, defs, memo, depth=0):
    """The same Int term with Real literals, or None when it reads an Int
    variable.  `to_real` distributes over ite and over + - *, so an Int term
    built only from numerals is the same number in either sort."""
    if depth > 200:
        return None
    if isinstance(node, str):
        if re.match(r"^[0-9]+$", node):
            return node + ".0"
        if node in memo:
            return memo[node]
        if node in defs and defs[node][0] == "Int":
            memo[node] = None                  # break cycles
            out = _realify(_sexp(defs[node][1]), defs, memo, depth + 1)
            memo[node] = out
            return out
        return None
    if not node:
        return None
    head = node[0]
    if head == "-" and len(node) == 2:
        arg = _realify(node[1], defs, memo, depth + 1)
        return None if arg is None else "(- %s)" % arg
    if head == "ite" and len(node) == 4:
        a = _realify(node[2], defs, memo, depth + 1)
        b = _realify(node[3], defs, memo, depth + 1)
        if a is None or b is None:
            return None
        return "(ite %s %s %s)" % (_print(node[1]), a, b)
    if head in REAL_OPS and len(node) >= 3:
        args = [_realify(a, defs, memo, depth + 1) for a in node[1:]]
        if any(a is None for a in args):
            return None
        return "(%s %s)" % (head, " ".join(args))
    return None


def _push_to_real(node, defs, memo, counts):
    """`node` with every `(to_real t)` over a constant Int term folded away."""
    if not isinstance(node, list) or not node:
        return node
    if node[0] == "to_real" and len(node) == 2:
        folded = _realify(node[1], defs, memo)
        if folded is not None:
            counts["to_real"] += 1
            return _sexp(folded)
    return [node[0]] + [_push_to_real(c, defs, memo, counts) for c in node[1:]]


def _resolve(node, defs, depth=0):
    """Follow definition names until the term is not a bare alias."""
    while isinstance(node, str) and node in defs and depth < 200:
        node = _sexp(defs[node][1])
        depth += 1
    return node


def _var_div(node, defs):
    """`floor(a/b)` for a divisor that is not a literal, written with `div`.

    MathSAT sends Int division through the reals, so a variable divisor comes
    back as `to_int(to_real a / to_real b)`.  SMT-LIB `div` is Euclidean and so
    rounds towards zero on a negative divisor, where `to_int` always rounds
    down; splitting on the sign is what makes the two agree.  Checked with Z3
    for every non-zero b: negating the equality is unsat, and dropping the
    split makes it sat (a = -2, b = -3).
    """
    node = _resolve(node, defs)
    if not (isinstance(node, list) and len(node) == 3 and node[0] == "/"):
        return None
    args = []
    for side in node[1:]:
        side = _resolve(side, defs)
        if not (isinstance(side, list) and len(side) == 2 and side[0] == "to_real"):
            return None
        args.append(_print(side[1]))
    a, b = args
    return "(ite (> %s 0) (div %s %s) (div (- %s) (- %s)))" % (b, a, b, a, b)


def restore_int_div(text):
    """Turn MathSAT's Real encoding of Int div/mod back into `div` and `mod`.

    Returns (text, counts).  Definitions left with no reader by the rewrite are
    dropped, so no `to_real` survives to fail the sort check; a definition that
    carries a VMT annotation (`(! ... :next ...)`) is never dropped, since that
    is what holds the model together.
    """
    counts = {"div": 0, "mod": 0, "dropped": 0, "rational": 0, "to_real": 0}
    lines = text.splitlines()
    body = {}                       # name -> body, for define-fun lines
    order = []                      # (index, name) in file order
    for i, ln in enumerate(lines):
        m = DEFINE.match(ln)
        if m:
            body[m.group(1)] = m.group(3)
            order.append((i, m.group(1), m.group(2)))

    # 1-2. Every `to_int` whose argument is a rational-linear combination of
    # integers becomes `(div N d)`.  That is the whole of MathSAT's Int-division
    # elimination, in one rule instead of a pattern per algebraic variant: the
    # plain quotient, the ceiling form `floor((x + k - 1)/k)`, and the sums of
    # several scaled terms the array benchmarks produce all reduce the same way.
    defs = {name: (sort, body[name]) for _, name, sort in order}
    memo = {}
    quot = {}
    for _, name, _sort in order:
        node = _sexp(body[name])
        if not (isinstance(node, list) and len(node) == 2 and node[0] == "to_int"):
            continue
        rewritten = _as_int_div(_linear(node[1], defs, memo))
        if rewritten is None:
            continue
        body[name] = rewritten
        counts["div"] += 1
        m = re.match(r"^\(div (\S+) (\d+)\)$", rewritten)
        if m:
            quot[name] = (m.group(1), m.group(2))

    # 2b. What is left over is a division whose divisor is not a literal, so
    #     there is no single denominator to put it over.  Those reduce with a
    #     sign split instead.
    for _, name, sort in order:
        if sort != "Int":
            continue
        node = _sexp(body[name])
        if not (isinstance(node, list) and len(node) == 2 and node[0] == "to_int"):
            continue
        rewritten = _var_div(node[1], defs)
        if rewritten is not None:
            body[name] = rewritten
            counts["div"] += 1
    defs = {name: (sort, body[name]) for _, name, sort in order}

    # 2c. And a `to_real` over an Int term with no Int variable in it is just
    #     the same number written in the other sort.
    rmemo = {}
    for _, name, _sort in order:
        if "to_real" not in body[name]:
            continue
        rebuilt = _print(_push_to_real(_sexp(body[name]), defs, rmemo, counts))
        if rebuilt != body[name]:
            body[name] = rebuilt
    defs = {name: (sort, body[name]) for _, name, sort in order}

    # 3. x + (-k)*(div x k)  ==  (mod x k).  `mod` is the operator MoXIchecker
    #    actually implements, so collapsing the pair is worth the extra pass.
    negp = {}
    for _, name, _sort in order:
        m = NEG_PROD.match(body[name])
        if m and m.group(2) in quot:
            x, k = quot[m.group(2)]
            if m.group(1) == k:
                negp[name] = (x, k)
    for _, name, _sort in order:
        m = SUM.match(body[name])
        if m and m.group(2) in negp:
            x, k = negp[m.group(2)]
            if m.group(1) == x:
                body[name] = "(mod %s %s)" % (x, k)
                counts["mod"] += 1

    # 4. Fold a rational coefficient in a Real definition into a decimal.
    for _, name, sort in order:
        if sort != "Real" or "(/ " not in body[name]:
            continue
        def fold(m):
            d = _decimal(int(m.group(1)), int(m.group(2)))
            if d is None:
                return m.group(0)
            counts["rational"] += 1
            return d
        body[name] = RAT.sub(fold, body[name])

    # 5. Drop definitions nothing reads any more.  Iterate: dropping one can
    #    orphan another.
    keep = {n for _, n, _ in order}
    while True:
        used = set()
        for i, ln in enumerate(lines):
            m = DEFINE.match(ln)
            if m:
                if m.group(1) not in keep:
                    continue
                text_i = body[m.group(1)]
            else:
                text_i = ln
            for tok in re.findall(r"[.\w$][.\w$!@%^&*+=<>?/-]*", text_i):
                used.add(tok)
        dead = {n for _, n, _ in order
                if n in keep and n not in used and "(!" not in body[n]}
        if not dead:
            break
        keep -= dead
        counts["dropped"] += len(dead)

    out = []
    for i, ln in enumerate(lines):
        m = DEFINE.match(ln)
        if not m:
            out.append(ln)
            continue
        if m.group(1) not in keep:
            continue
        out.append("(define-fun %s () %s %s)" % (m.group(1), m.group(2), body[m.group(1)]))
    return "\n".join(out) + "\n", counts


if __name__ == "__main__":
    text = sys.stdin.read()
    new, mapping = sanitize(text)
    new, counts = restore_int_div(new)
    sys.stdout.write(new)
    if "--report" in sys.argv:
        sys.stderr.write("renamed %d symbols\n"
                         % sum(1 for k, v in mapping.items() if k != v))
        sys.stderr.write("div %(div)d mod %(mod)d rational %(rational)d dropped %(dropped)d\n" % counts)
