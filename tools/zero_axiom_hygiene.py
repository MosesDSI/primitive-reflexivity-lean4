"""Lexer-aware hygiene scan for zero-axiom Lean 4 files.

Implements Section 2 of the "Zero-Axiom Lean 4 Verification & Hygiene
Standard" in AGENTS.md. It is the second line of defense; the kernel axiom
audit (`axiom-audit` with an empty allowlist, or `#print axioms`) is the
ground truth.

Method:
  1. Strip nested block comments (/- ... -/), line comments (--) and string
     literals ("...") while keeping line numbers.
  2. Match tokens as whole lexical tokens, case-sensitively. No line is ever
     excluded, so `grind` is caught even on a line that also says `Lean.Grind`.

Report kinds:
  FORBIDDEN  banned token; exit status 1.
  MACRO      a ZeroInt macro (nat_ring / int_ring / int_transfer). Allowed only
             inside ZeroInt.lean itself (the sanctioned exception).
  REVIEW     binary `-`, `/`, `%`, or Nat.sub / Nat.div / Nat.pred / Nat.mod.
             Must be checked by hand: Int subtraction and negation are allowed;
             a written Nat subtraction, division or modulo is not, unless
             explicitly accepted (e.g. `x % 0` in the characteristic-0 reading).

Usage:
  python -I tools/zero_axiom_hygiene.py --selftest
  python -I tools/zero_axiom_hygiene.py FILE.lean [FILE.lean ...]
"""
import os
import re
import sys

FORBIDDEN = [
    # from the standard
    "sorry", "admit", "axiom", "opaque", "unsafe", "partial", "implemented_by",
    "extern", "grind", "omega", "simp", "decide", "native_decide", "linarith",
    "ring", "norm_num", "Classical", "Quot",
    # further automation and axiom-bearing names
    "simp_all", "simpa", "simp_arith", "by_cases", "aesop", "nlinarith",
    "positivity", "ring_nf", "field_simp", "tauto", "propext", "funext",
    "Decidable.em", "Real", "Float", "Rat",
]
MACROS = ["nat_ring", "int_ring", "int_transfer"]
_LEFT = r"(?<=[\w)\]'₀-₉])"
_RIGHT = r"(?=[\w(\[↑])"
REVIEW = [
    ("binary -", _LEFT + r"\s*-\s*" + _RIGHT),
    ("binary /", _LEFT + r"\s*/\s*" + _RIGHT),
    ("binary %", _LEFT + r"\s*%\s*" + _RIGHT),
    ("Nat.sub", r"\bNat\.sub\b"), ("Nat.div", r"\bNat\.div\b"),
    ("Nat.pred", r"\bNat\.pred\b"), ("Nat.mod", r"\bNat\.mod\b"),
    ("HSub", r"\bHSub\b"), ("HDiv", r"\bHDiv\b"), ("HMod", r"\bHMod\b"),
]


def strip(src: str) -> str:
    """Blank out comments and string literals, keeping line structure."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if src.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        if src[i] == '"':
            out.append(" ")
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\" and i + 1 < n:
                    out.append(" ")
                    i += 1
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
            out.append(" ")
            i += 1
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def _token(tok: str) -> re.Pattern:
    return re.compile(r"(?<![\w.'])" + re.escape(tok) + r"(?![\w'])")


_FORBIDDEN_RE = [(t, _token(t)) for t in FORBIDDEN]
_MACRO_RE = [(t, _token(t)) for t in MACROS]
_REVIEW_RE = [(name, re.compile(p)) for name, p in REVIEW]


def scan_text(text: str):
    hits = []
    for ln, line in enumerate(strip(text).splitlines(), 1):
        for t, r in _FORBIDDEN_RE:
            if r.search(line):
                hits.append(("FORBIDDEN", ln, t, line.strip()))
        for t, r in _MACRO_RE:
            if r.search(line):
                hits.append(("MACRO", ln, t, line.strip()))
        for name, r in _REVIEW_RE:
            if r.search(line):
                hits.append(("REVIEW", ln, name, line.strip()))
    return hits


# (kind, line, token) triples the fixture must produce, and nothing else.
_EXPECTED = {
    ("FORBIDDEN", 4, "grind"), ("FORBIDDEN", 5, "simp"), ("FORBIDDEN", 6, "omega"),
    ("REVIEW", 8, "binary -"), ("FORBIDDEN", 11, "Classical"), ("MACRO", 12, "nat_ring"),
    ("REVIEW", 13, "binary -"), ("REVIEW", 14, "binary /"), ("REVIEW", 15, "binary %"),
    ("FORBIDDEN", 16, "Quot"), ("FORBIDDEN", 17, "unsafe"),
    ("FORBIDDEN", 18, "implemented_by"), ("FORBIDDEN", 18, "opaque"),
}


def selftest() -> bool:
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "hygiene_selftest_fixture.lean.txt")
    got = {(k, ln, t) for k, ln, t, _ in scan_text(open(path, encoding="utf-8").read())}
    missing, extra = _EXPECTED - got, got - _EXPECTED
    for m in sorted(missing):
        print(f"SELFTEST MISSED  {m}")
    for e in sorted(extra):
        print(f"SELFTEST SPURIOUS {e}")
    ok = not missing and not extra
    print(f"selftest: {'PASS' if ok else 'FAIL'} ({len(got)} hits, {len(_EXPECTED)} expected)")
    return ok


def main(argv) -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    if argv == ["--selftest"]:
        return 0 if selftest() else 2
    if not argv:
        print(__doc__)
        return 2
    bad = False
    for p in argv:
        hits = scan_text(open(p, encoding="utf-8").read())
        c = {k: sum(1 for h in hits if h[0] == k) for k in ("FORBIDDEN", "MACRO", "REVIEW")}
        print(f"== {p}: FORBIDDEN={c['FORBIDDEN']} MACRO={c['MACRO']} REVIEW={c['REVIEW']}")
        for kind, ln, t, text in hits:
            print(f"   {kind:9} L{ln:<4} [{t}] {text[:110]}")
        bad = bad or c["FORBIDDEN"] > 0
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
