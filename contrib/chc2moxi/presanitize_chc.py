#!/usr/bin/env python3
"""Rewrite a CHC source file into the SMT-LIB subset MathSAT's parser accepts.

`horn2vmt` reads its input with MathSAT, which is strict where Z3 is lenient.
Four constructs that CHC-COMP files contain make MathSAT stop with a parse
error before any translation happens.  Each is rewritten here into a form
MathSAT does accept, and each rewrite is applied only where it is provably
meaning-preserving; anything outside that guard is left untouched, so the file
still fails and is still excluded rather than being translated to something
that is not the original problem.

  1. n-ary `concat`.  SMT-LIB declares `concat` binary.  Z3 accepts a chain and
     reads it left-associatively, so `(concat a b c)` becomes
     `(concat (concat a b) c)` -- the same term, spelled the way MathSAT wants.

  2. `bvudiv_i`, `bvsdiv_i`, `bvurem_i`, `bvsrem_i`, `bvsmod_i`.  These are Z3's
     *internal* division symbols.  Z3 defines the SMT-LIB operator as
     `bvudiv x y = ite (y = 0) all-ones (bvudiv_i x y)`, so the `_i` form agrees
     with the standard operator exactly when the divisor is non-zero and is
     otherwise uninterpreted.  The rewrite therefore fires **only when the
     divisor is a non-zero bit-vector literal**, where the two are the same
     function.  A non-constant divisor is left alone.

  3. `rem`.  Not an SMT-LIB Int symbol; Z3 has it, with the sign of the result
     following the divisor: `rem(a,b) = mod(a,b)` for `b > 0` and `-mod(a,b)`
     for `b < 0`.  The rewrite fires **only for a positive integer literal
     divisor**, where `rem` and `mod` coincide.

  4. Symbols delimited by runs of backslashes (`\\\\\\tuple(x, y)\\\\\\`), which a
     few 2019 array files carry.  A backslash is not in the SMT-LIB simple
     symbol character set and the file does not parse anywhere.  The delimiters
     are replaced by pipes, which is what the symbol was meant to be.

Usage:  presanitize_chc.py < in.smt2 > out.smt2
        presanitize_chc.py --report < in.smt2 > out.smt2   (counts on stderr)
"""
import re
import sys

# A run of two or more backslashes used as a symbol delimiter.  The body is
# taken up to the next such run on the same line; it may hold anything but a
# pipe or a newline, which is exactly what a quoted symbol may hold.
BACKSLASH_SYM = re.compile(r"\\{2,}([^|\\\n]*)\\{2,}")

DIV_I = {
    "bvudiv_i": "bvudiv",
    "bvsdiv_i": "bvsdiv",
    "bvurem_i": "bvurem",
    "bvsrem_i": "bvsrem",
    "bvsmod_i": "bvsmod",
}

BV_LIT = re.compile(r"^(?:#b[01]+|#x[0-9a-fA-F]+)$")
NUMERAL = re.compile(r"^[0-9]+$")


def _bv_is_zero(tok):
    """True when tok is a bit-vector literal denoting 0."""
    if not BV_LIT.match(tok):
        return None                      # not a literal at all
    return set(tok[2:]) <= {"0"}


def tokenize(text):
    """SMT-LIB tokens: parens, |quoted|, "strings", ;comments, everything else."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c in "()":
            out.append(c)
            i += 1
        elif c in " \t\r\n":
            j = i
            while j < n and text[j] in " \t\r\n":
                j += 1
            out.append(text[i:j])
            i = j
        elif c == ";":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(text[i:j])
            i = j
        elif c == "|":
            j = text.find("|", i + 1)
            j = n - 1 if j < 0 else j
            out.append(text[i:j + 1])
            i = j + 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            out.append(text[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < n and text[j] not in "()|; \t\r\n\"":
                j += 1
            out.append(text[i:j])
            i = j
    return out


def parse(tokens):
    """Nested lists of tokens.  Whitespace and comments are dropped; the output
    is re-printed with canonical spacing, which SMT-LIB is indifferent to."""
    stack, cur = [], []
    for t in tokens:
        if t == "(":
            stack.append(cur)
            cur = []
        elif t == ")":
            if not stack:
                continue
            done, cur = cur, stack.pop()
            cur.append(done)
        elif t[:1] in (";",) or t.strip() == "":
            continue
        else:
            cur.append(t)
    while stack:
        done, cur = cur, stack.pop()
        cur.append(done)
    return cur


def unparse(node, out):
    if isinstance(node, list):
        out.append("(")
        for k, c in enumerate(node):
            if k:
                out.append(" ")
            unparse(c, out)
        out.append(")")
    else:
        out.append(node)


def rewrite(node, counts):
    if not isinstance(node, list):
        return node
    node = [rewrite(c, counts) for c in node]
    if not node or not isinstance(node[0], str):
        return node
    head = node[0]

    if head == "concat" and len(node) > 3:
        counts["concat"] += 1
        acc = node[1]
        for arg in node[2:]:
            acc = ["concat", acc, arg]
        return acc

    if head in DIV_I and len(node) == 3:
        zero = _bv_is_zero(node[2]) if isinstance(node[2], str) else None
        if zero is False:
            counts[head] += 1
            return [DIV_I[head]] + node[1:]
        counts["unguarded-" + head] += 1
        return node

    if head == "rem" and len(node) == 3 and isinstance(node[2], str):
        if NUMERAL.match(node[2]) and int(node[2]) > 0:
            counts["rem"] += 1
            return ["mod"] + node[1:]
        counts["unguarded-rem"] += 1
        return node

    return node


def presanitize(text):
    import collections
    counts = collections.Counter()

    def _pipe(m):
        counts["backslash-symbol"] += 1
        return "|" + m.group(1) + "|"

    if "\\\\" in text:
        text = BACKSLASH_SYM.sub(_pipe, text)

    tokens = tokenize(text)

    # `parse` closes an unclosed list and drops a stray `)`, so on a file whose
    # parentheses do not balance it would silently invent a different problem.
    # Such a file is handed back untouched and fails in horn2vmt exactly as it
    # did before.
    depth = 0
    for t in tokens:
        if t == "(":
            depth += 1
        elif t == ")":
            depth -= 1
            if depth < 0:
                break
    if depth != 0:
        counts["unbalanced"] += 1
        return text, counts

    tree = parse(tokens)
    tree = [rewrite(t, counts) for t in tree]
    out = []
    for t in tree:
        unparse(t, out)
        out.append("\n")
    return "".join(out), counts


if __name__ == "__main__":
    new, counts = presanitize(sys.stdin.read())
    sys.stdout.write(new)
    if "--report" in sys.argv:
        for k, v in sorted(counts.items()):
            sys.stderr.write("%s\t%d\n" % (k, v))


# ---------------------------------------------------------------------------
# Head normalisation.
#
# horn2vmt reads the head of a clause positionally: argument i of the predicate
# is state variable i.  When an argument is a literal or a repeated variable
# there is no variable to bind and it dereferences a null -- the process dies
# with SIGSEGV rather than a diagnostic.  Rewriting
#
#     (forall (x)   (=> body (P x 0)))
# to  (forall (x v) (=> (and body (= v 0)) (P x v)))
#
# is the textbook CHC head normalisation: same models, one fresh variable per
# offending argument.  It is applied only as a retry, after horn2vmt has already
# refused the file, so a task that translates today is never touched by it.

def _decl_sorts(tree):
    """Argument sorts of every declared predicate, by symbol."""
    sorts = {}
    for cmd in tree:
        if (isinstance(cmd, list) and len(cmd) == 4 and cmd[0] == "declare-fun"
                and isinstance(cmd[2], list) and cmd[3] == "Bool" and cmd[2]):
            sorts[cmd[1]] = cmd[2]
    return sorts


def _normalize_clause(node, sorts, counts):
    if not (isinstance(node, list) and len(node) == 2 and node[0] == "assert"):
        return node
    body = node[1]
    quant, binds = None, []
    if isinstance(body, list) and len(body) == 3 and body[0] in ("forall", "exists"):
        quant, binds, body = body[0], body[1], body[2]
    if quant == "exists" or not isinstance(binds, list):
        return node

    ante, head = None, body
    if isinstance(body, list) and len(body) == 3 and body[0] == "=>":
        ante, head = body[1], body[2]
    if not (isinstance(head, list) and len(head) >= 2 and isinstance(head[0], str)):
        return node
    pred = head[0]
    if pred not in sorts or len(sorts[pred]) != len(head) - 1:
        return node

    bound = {b[0] for b in binds if isinstance(b, list) and b}
    args, extra, eqs, seen = [], [], [], set()
    for i, arg in enumerate(head[1:]):
        if isinstance(arg, str) and arg in bound and arg not in seen:
            seen.add(arg)
            args.append(arg)
            continue
        fresh = ".hn%d" % i
        while fresh in bound or fresh in seen:
            fresh += "_"
        seen.add(fresh)
        args.append(fresh)
        extra.append([fresh, sorts[pred][i]])
        eqs.append(["=", fresh, arg])

    if not eqs:
        return node
    counts["head-normalised"] += 1
    conj = ([ante] if ante is not None else []) + eqs
    new_ante = conj[0] if len(conj) == 1 else ["and"] + conj
    new_body = ["=>", new_ante, [pred] + args]
    return ["assert", ["forall", binds + extra, new_body]]


def normalize_heads(text):
    """`text` with every clause head reduced to distinct bound variables."""
    import collections
    counts = collections.Counter()
    tokens = tokenize(text)
    depth = 0
    for t in tokens:
        if t == "(":
            depth += 1
        elif t == ")":
            depth -= 1
            if depth < 0:
                break
    if depth != 0:
        counts["unbalanced"] += 1
        return text, counts
    tree = parse(tokens)
    sorts = _decl_sorts(tree)
    if not sorts:
        return text, counts
    tree = [_normalize_clause(c, sorts, counts) for c in tree]
    out = []
    for t in tree:
        unparse(t, out)
        out.append("\n")
    return "".join(out), counts
