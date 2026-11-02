# CI Run #51: Docgen Homepage and Theta__0_Photon Executable Repair

**Date:** 2026-11-01
**Project:** `PrimitiveReflexivity`, CI workflow and `Theta__0_Photon/`
**Toolchain:** `leanprover/lean4:v4.33.1` (local Windows install via elan), Mathlib `v4.33.1` (`0df444a`)
**Branch:** `ci/fix-docgen-homepage-and-theta-exe`, commit `226b468`, **not pushed**

## Objective

Jonathon asked what happened in "docs: retitle the LTromino axiom-audit note and record its rules wher… #51". The `#51` is the run number of the **Lean Action CI** workflow for the push of `ac54a29` (which also carried `478654b`), not a PR or an issue. That run failed. Jonathon then asked for both failures to be fixed on a branch.

## Diagnosis

The `ltromino` and `simulation-exchange` jobs passed. The `ltromino` axiom audit reported 400 declarations within `[]`. Two other jobs failed for unrelated reasons.

1. **`build`: caused by this push.**
   - `leanprover-community/docgen-action@v1` has an input `homepage` with default `docs`. If that folder exists, the action treats it as a Jekyll site and runs `bundle exec jekyll build` in it.
   - Before `478654b` the repo had no `docs/`, so the Jekyll steps were skipped. `478654b` created `docs/notes/`.
   - Result: `Could not locate Gemfile or .bundle/ directory`, exit 10. The Lean build itself passed, and the previous run (`bf11b64`) had a green `build`.
2. **`theta-0-photon`: failing on every run since the job was added (`ci: wire Theta__0_Photon into the root CI workflow`, 2026-10-11).**
   - `Theta__0_Photon/lakefile.toml` made `[[lean_exe]] theta__0_photon` (root `Main`) the default target.
   - `Main.lean` holds theorems and no `def main`, so the link step failed with `ld.lld: error: undefined symbol: main`.
   - The library always compiled; only the final step `[5252/5252] Building theta__0_photon:exe` failed. Because `lake build` failed, this job's leanchecker and axiom-audit steps **had never run**.
   - This was already noted as pre-existing in `Theta__0_Photon/2026-09-06_Theta0Photon_Build_Summary.md` (lines 350–351). In Part 3 of `2026-10-15_LTromino_Outside_Build_Verification.md`, Jonathon had asked to leave it alone. This session Jonathon asked for it to be fixed.

## What Was Changed (commit `226b468`)

- `.github/workflows/lean_action_ci.yml`: the docgen step now has `with: homepage: homepage`, with a comment.
  - The folder `homepage/` **must not exist** in the repository. The action checks `[ -d homepage ]` before any build step. When the folder is absent, it skips Jekyll and uploads only the API docs, which matches the behaviour before `docs/` existed.
  - Moving `docs/notes/` was rejected, because `AGENTS.md` and `ROADMAP_LEDGER.md` link to it.
- `Theta__0_Photon/lakefile.toml`: the `[[lean_exe]]` block is replaced by `[[lean_lib]] name = "Main"`, and `defaultTargets = ["Theta0Photon", "Main"]`. A comment explains why.
  - `Main.lean`'s theorems are still built, so they now reach leanchecker and axiom-audit.

No `.lean` file was changed.

## Problems Encountered and How They Were Fixed (local environment)

- **The `Theta__0_Photon/.lake/packages` tree was an empty shell.** It held 4,069 directories, 0 files, all dated 2026-10-23.
  - Jonathon believes an earlier Claude Code instance moved the work from C: to D: and the files were lost then.
  - Because `packages/mathlib` had no `.git` contents, `lake` ran git against the **outer** repo, reported "mathlib: URL has changed", and failed checking out `0df444a`. Plain `lean` could not find `Mathlib/Data/Real/Basic.olean` either.
  - Only Theta was affected. The root project's Mathlib is intact (source, `.git`, oleans). `LTromino` and `SimulationExchange` are core-only.
  - I confirmed zero files before running `rm -r .lake/packages`. `.lake/build` (217 files) was kept.
- **Cloning Mathlib from GitHub failed twice** (`curl 56 Recv failure: Connection was reset`, then `schannel: server closed abruptly`; both `early EOF`). The connection dropped during the multi-GB clone.
  - Workaround: every git dependency in `Theta__0_Photon/lake-manifest.json` is at the same rev as in the root `lake-manifest.json`. Each of the nine (mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli) was cloned **locally** from `../.lake/packages/<name>`, its `origin` was set to the manifest URL, and the manifest rev was checked out. Each HEAD was verified.
  - `lake exe cache get` then found all 8,689 files already in the user cache: "No files to download", decompressed in about 12 minutes.
- **Windows long paths were disabled** (`LongPathsEnabled = 0`, no `core.longpaths`). This was probably the cause of the earlier `leantar` `os error 3` failures recorded in `Theta__0_Photon/2026-09-11_ContinuumBridge_and_OpenAI_Comparative_Audit.md` §5.
  - Jonathon ran it as admin; it is now `LongPathsEnabled = 1` and `git config --system core.longpaths true`, both verified.
  - Pasting long commands into the admin PowerShell window broke them across lines. What worked: a script file in the user home folder, run with `pwsh -ExecutionPolicy Bypass -File longpaths.ps1`, then deleted.
  - The cache decompression above ran with no path errors.

## What Was Tested and What Results Mean

```
lake build  (Theta__0_Photon, on the branch)   # Build completed successfully (2635 jobs), exit 0; no exe link step
lake build Main                                # Build completed successfully (2634 jobs)
#print axioms on Main's five theorems          # zeroProcess, zero_is_not_a_coordinate, Photon,
                                               # Superposition, EncryptedPacket: "does not depend on any axioms"
```

- The rest of `Theta0Photon` prints `[propext, Classical.choice, Quot.sound]` in places. That is within the CI job's default allowlist, so the newly reachable axiom-audit step is expected to pass.
- **Not tested locally:**
  - the docgen change, which only runs on GitHub Actions;
  - `leanchecker` and `axiom-audit` for Theta, which have never run in CI. If either reports something on first run, that is a real finding about the Theta package, not about this fix.

## Final State

- Commit `226b468` on branch `ci/fix-docgen-homepage-and-theta-exe` (from `master` at `ac54a29`). **Not pushed.**
- `master` is unchanged, and so is the working tree apart from this summary, which is untracked.
- The Theta local environment builds again. Windows long paths are on.

## Next Steps

1. With Jonathon's go-ahead, push the branch and open a PR so CI runs all four jobs.
2. Check in the CI log that:
   - `build`: the docgen step prints "The 'homepage' folder does not exist" and the Jekyll steps are skipped;
   - `theta-0-photon`: `lake build` passes, then leanchecker and axiom-audit both finish green.
3. If the Theta audit or leanchecker fails, investigate that as a new finding. Do not widen the allowlist to make it pass.
4. Once merged, optionally note in `Theta__0_Photon/2026-09-06_Theta0Photon_Build_Summary.md` that the exe link failure is resolved.
