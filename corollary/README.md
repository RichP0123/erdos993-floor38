# The compiled Mathlib floor38 corollary

The completed local proof includes this universe-polymorphic theorem:

```lean
Erdos993.ForestCore.mathlib_forest_unimodal_through_thirty_seven :
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    Fintype.card V ≤ 37 → G.IsAcyclic →
      Erdos993.Unimodal (fun k => (G.indepSetFinset k).card)
```

Thus every finite simple forest through 37 vertices has a unimodal independence
sequence. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
There is no assumed original floor theorem left in this final statement.

The five ordinary Lean modules in `src/ForestCore/` were compiled against the
original audited graph foundation. `Graph` translates Boolean adjacency;
`AcyclicBridge` proves equivalence with Mathlib acyclicity; `CountingBridge`
proves the exact independent-set counting bijection; `Transfer` transports a
general finite bound to arbitrary finite vertex types; `MathlibFloor38Target`
defines the independent target and proves a conditional specialization helper.

The native source `../tools/MathlibFloor38Assembler.lean` supplies the already
proved original floor38 theorem to that helper and submits the resulting term
to Lean's kernel with checking enabled. It exports the actual theorem, then
fresh-process reimport checks its literal type, universe parameters and theorem
kind and kernel-checks an alias. The new complete import union was checked by
`../tools/MathlibFloor38ImportUnionAudit.lean` with zero conflicts.

Both native tools preserve the reviewed original loader: unchanged original
declaration objects, types and bodies remain in the original module data;
only the dependency dictionary is restricted. The loader checks dependency
closure, original ownership and cached axioms, traversing uncached theorem
bodies. It never replaces theorems with axioms. Historical "experiment" wording
in a copied source header is preserved verbatim; the completed status is
recorded in the evidence summary.

`PROOF_EVIDENCE_SUMMARY.json` is a public derivative of the completed private
receipts, with their hashes. It is **not a newly issued compiler receipt**.
Raw local commands and machine paths are omitted. The original full proof was
reused from its successful complete audit, without redoing its large finite
computation or a new whole-corpus hash pass. The corollary added five small
ordinary compilations, kernel assembly, reimport, and an enlarged union audit.
Peak private memory for that local pipeline was 951.1 MiB. Compiled objects and
executables are not included here; their measured hashes are in the summary.

## What can be reproduced here

Run from the repository root:

```text
python tools/verify_corollary_sources.py
```

This checks all seven exact source files and the selected public support files.
It runs no compiler. The Lean files retain the exact successful local bytes.

The separate `../core/` package contains ordinary reusable proofs, including
the generic transport, and has a completed local ordinary Lake build. It does
not contain the large finite census needed to instantiate floor38. Its generic
transport theorem retains the finite-bound premise.

For the full original proof, obtain the separate frozen
`floor38_unconditional_lean_sources_2026-09-28.zip` release asset and follow its
`REPRODUCTION.md`. That asset includes all finite data and the prepared
`portable_build_floor38.py`. A complete fresh run of that exported portable
workflow has not been exercised; neither has the public manual procedure below.
The original local proof, the ordinary core build, and the local corollary run
have completed successfully. These are distinct claims.

## Manual corollary rebuild after a successful full rebuild

Use Lean 4.30.0 at commit `d024af099ca4bf2c86f649261ebf59565dc8c622` and the exact
Mathlib/package revisions in the extracted full archive's `lake-manifest.json`.
The full runner checks those dependencies. Its completed native build must have
`.floor38-build/native/REBUILD_RESULT.json` with `success: true` and the actual
floor38 theorem. The original corpus remains necessary: these seven small
files are not a standalone replacement for it.

The following Bash commands are an explicit unexecuted public recipe. On
Windows the same executable arguments apply with `.exe` suffixes and a
semicolon-separated `LEAN_PATH`; use the installed toolchain binaries directly.
Substitute absolute local paths for these four variables:

```bash
R=/absolute/path/to/this/repository
F=/absolute/path/to/extracted/full-source-release
T=/absolute/path/to/lean-toolchain
M=/absolute/path/to/locked-mathlib-project
B="$R/.corollary-build"
export PATH="$T/bin:$PATH"
mkdir -p "$B/lib/ForestCore" "$B/bin" "$B/logs"
```

Let `PACKAGES` be the colon-separated compiled package directories
`$M/.lake/packages/<package-name>/.lake/build/lib/lean` for every package in the
full archive's `lake-manifest.json`. Use the exact locked package set. Exclude
both the Mathlib project's own project-object directory and the separate core
package's object directory. In particular, `ForestStatements` must resolve to
the object produced by the **full proof build**.

Compile only the five small modules, preserving their logical names by running
from the supplied `corollary/src` directory:

```bash
export LEAN_PATH="$B/lib:$F/.floor38-build/native/lib:$F/.floor38-build/common/lib:$PACKAGES"
unset LEAN_SYSROOT
cd "$R/corollary/src"
for module in Graph AcyclicBridge CountingBridge Transfer MathlibFloor38Target; do
  "$T/bin/lean" -DmaxRecDepth=4096 -o "$B/lib/ForestCore/$module.olean" "ForestCore/$module.lean" > "$B/logs/$module.log" 2>&1 || exit 1
done
```

Build each native helper against bundled Lean only. Clear project imports for
this compilation so private Lean APIs cannot be shadowed:

```bash
for module in MathlibFloor38Assembler MathlibFloor38ImportUnionAudit; do
  LEAN_PATH="" "$T/bin/lean" -c "$B/bin/$module.c" "$R/tools/$module.lean" || exit 1
  "$T/bin/leanc" -O2 -o "$B/bin/$module" "$B/bin/$module.c" || exit 1
done
```

Restore/retain the runtime `LEAN_PATH` above and run all three checks:

```bash
"$B/bin/MathlibFloor38Assembler" assemble ForestCore.MathlibFloor38 "$B/lib/ForestCore/MathlibFloor38.olean" > "$B/logs/assembly.log" 2>&1 || exit 1
sha256sum "$B/lib/ForestCore/MathlibFloor38.olean" > "$B/final.sha256"
"$B/bin/MathlibFloor38Assembler" verify ForestCore.MathlibFloor38Reimport "$B/lib/ForestCore/MathlibFloor38Reimport.olean" > "$B/logs/reimport.log" 2>&1 || exit 1
"$B/bin/MathlibFloor38ImportUnionAudit" > "$B/logs/import-union.log" 2>&1 || exit 1
sha256sum -c "$B/final.sha256" || exit 1
```

Each command must exit successfully. Preserve logs, source hashes, compiler
hashes, dependency/object hashes and available `.olean.server`, `.olean.private`
and `.ir` companions. Hash the final object immediately after assembly and
confirm those same bytes survive reimport and the union check. Require the
markers and signatures listed in `REVIEWER_CHECKLIST.md`; successful source
compilation alone is insufficient. This recipe supplies concrete commands,
not a new certified portable runner or a resource-limit mechanism.
