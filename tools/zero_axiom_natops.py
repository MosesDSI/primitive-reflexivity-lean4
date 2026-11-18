"""Mechanical check for *written* Nat subtraction, division and modulo.

Complements tools/zero_axiom_hygiene.py (lexical) and the kernel axiom audit.
For every declaration of the given modules it walks the fully elaborated type
and value and reports:

  * `HSub.hSub`, `HDiv.hDiv`, `HMod.hMod` applied at type `Nat`;
  * direct uses of `Nat.sub`, `Nat.pred`, `Nat.div`, `Nat.mod`.

Only each declaration's own term is inspected, not its dependencies, so this
answers "did we write it?" (AGENTS.md: reaching these only through core's
definitions of Int and <= is accepted).

Usage (run from the repository root):
  python -I tools/zero_axiom_natops.py --selftest
  python -I tools/zero_axiom_natops.py PACKAGE_DIR ROOT_MODULE [--allow DECL ...]

All modules named ROOT_MODULE or ROOT_MODULE.* are scanned. Hits on a
declaration listed with --allow are reported as ALLOWED; any other hit makes
the exit status 1.

Accepted exceptions (AGENTS.md), for SimulationExchange:
  --allow SimulationExchange.ZeroGrind.mod_zero' --allow Nat.mod.eq_def
  --allow SimulationExchange.ZeroInt.sub_shift --allow SimulationExchange.ZeroInt.sub_shift._f
"""
import os
import subprocess
import sys
import tempfile

LEAN_TEMPLATE = r'''
import Lean
import {root}
open Lean Elab Command
elab "#nat_ops_all" : command => do
  let env ← getEnv
  let root : Name := `{root}
  let mut n : Nat := 0
  for (name, ci) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if m == root || root.isPrefixOf m then
        n := n + 1
        let exprs := [ci.type] ++ (match ci.value? with | some v => [v] | none => [])
        for e in exprs do
          let found := e.foldConsts (init := ([] : List Name)) fun c acc =>
            if c == ``Nat.sub || c == ``Nat.pred || c == ``Nat.div || c == ``Nat.mod then
              c :: acc else acc
          for f in found do logInfo m!"HIT {{name}} uses {{f}}"
          let ops := e.find? fun sub =>
            (sub.isAppOfArity ``HSub.hSub 6 || sub.isAppOfArity ``HDiv.hDiv 6 ||
             sub.isAppOfArity ``HMod.hMod 6) && sub.getArg! 0 == mkConst ``Nat
          if let some o := ops then logInfo m!"HIT {{name}} Nat-operator {{o.getAppFn.constName!}}"
    | none => pure ()
  logInfo m!"SCANNED {{n}}"
#nat_ops_all
'''


def run(package_dir: str, root: str):
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "NatOpsCheck.lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(LEAN_TEMPLATE.format(root=root))
        out = subprocess.run(["lake", "env", "lean", path], cwd=package_dir,
                             capture_output=True, text=True, encoding="utf-8")
    lines = (out.stdout + out.stderr).splitlines()
    errors = [l for l in lines if "error" in l]
    hits, scanned = [], None
    for l in lines:
        t = l.split("info: ", 1)[-1]
        if t.startswith("HIT "):
            parts = t.split(" ", 2)
            hits.append((parts[1], parts[2]))
        elif t.startswith("SCANNED "):
            scanned = int(t.split()[1])
    return scanned, hits, errors


def main(argv) -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    if argv == ["--selftest"]:
        here = os.path.dirname(os.path.abspath(__file__))
        pkg = os.path.join(os.path.dirname(here), "SimulationExchange")
        scanned, hits, errors = run(pkg, "SimulationExchange.ZeroInt")
        found = {decl for decl, _ in hits}
        ok = not errors and "SimulationExchange.ZeroInt.sub_shift" in found
        print(f"selftest: {'PASS' if ok else 'FAIL'} "
              f"(positive control ZeroInt.sub_shift {'detected' if ok else 'NOT detected'}; "
              f"{scanned} declarations scanned)")
        for e in errors:
            print("  ", e)
        return 0 if ok else 2
    if len(argv) < 2:
        print(__doc__)
        return 2
    pkg, root, rest = argv[0], argv[1], argv[2:]
    allow = {rest[i + 1] for i in range(len(rest) - 1) if rest[i] == "--allow"}
    scanned, hits, errors = run(pkg, root)
    if errors or scanned is None:
        print("ERROR running the check:")
        for e in errors:
            print("  ", e)
        return 2
    bad = [(d, w) for d, w in hits if d not in allow]
    print(f"== {root}: {scanned} declarations scanned, "
          f"{len(hits) - len(bad)} allowed, {len(bad)} unallowed Nat sub/div/mod")
    for d, w in hits:
        print(f"   {'ALLOWED' if d in allow else 'HIT':8} {d} {w}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
