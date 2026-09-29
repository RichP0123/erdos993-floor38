# General forest independence-polynomial library

This small Lean 4.30 / Mathlib package extracts reusable general results from the completed finite forest project and adds conventional Mathlib-facing interfaces. The preserved source closure contains **108 modules, 555,087 bytes**; `SOURCE_PROVENANCE.json` identifies their exact audited originals and hashes. The new `ForestCore/` interface modules are separate work and require their own successful build receipt.

The intended general interface covers finite graph representation/counting, forest acyclicity, transfer to finite vertex types, sequence properties and linear certificate reasoning. Consult the actual exported declarations: a small-library build does not prove every forest through 37 unless the complete finite bank and case certificates are also supplied.

## Build status and scope

The original project's complete finite theorem was checked and audited separately. The frozen full-source release is `floor38_unconditional_lean_sources_2026-09-28.zip`; its SHA-256 is `c0d65a24e6eb5fbe09f4ee3d00a1283dbc72a458429c5c6bd5486abc66e65960`. Its native final assembly/custom-loader reimport, full-import compatibility check and exact certificate evidence are described in that release. This small package does not reproduce those 17,486 project modules or certify the full archive by implication.

**The complete ordinary Lake build passed on 28 September 2026: 116 project modules, 735.526 seconds.** It ran in a fresh source directory with no copied project proof objects, using installed locked upstream caches. The command was `lake --no-cache --no-ansi build`; no custom loader or assembler was used. The source-hashed receipt and printed axiom checks are summarized in `BUILD_EVIDENCE.json`. Peak sampled process-tree private memory was approximately 659 MiB; this excludes shared/mapped memory and is not a total RAM requirement. Preserved sources produced some style-linter warnings, but no proof error or admission. This was a fresh directory on the same computer, not an independent-machine reproduction.

No full fresh portable build of the complete floor38 archive is claimed here. Historical comments inside byte-preserved sources describe the original writing sessions; the new build receipt gives their current compilation status.

## Main reusable declarations

Import `ForestCore.Transfer` for the graph bridge, `ForestCore.SequenceBridge` for the alternate sequence interface, `ForestCore.LinearCertificate` for rational certificate algebra, or `ForestCore` for all general results.

| Declaration (under `Erdos993.ForestCore`) | Meaning |
|---|---|
| `isForest_iff_isAcyclic` | Exact equivalence of the original forest predicate and Mathlib's acyclicity |
| `coefficient_eq_card_indepSetFinset` | Original ordinary coefficients equal Mathlib independent-set counts |
| `independentCoefficient_iso` | Counts are invariant under graph isomorphism |
| `transfer_forest_bound` | Transports an explicitly supplied bound theorem to arbitrary finite vertex types |
| `unimodal_iff_monotone_sides` | Adjacent inequalities and two-sided peak monotonicity are equivalent |
| `card_indepSetFinset_eq_filtered_powerset` | Two standard independent-set counting interfaces coincide |
| `LinearCertificate.first_layer_certificate_sound` | General rational residual bound from explicit valid rows and nonnegative weights/masses |

The general preserved layer includes actual-graph vertex recurrence, multiplication on separated vertex sets, interval soundness, certificate acceptance/split coverage, log-concavity cross inequalities and convolution closure. Each lemma retains its stated hypotheses; the package does not hide a finite-bound assumption inside an unconditional floor theorem.

## Existing local prerequisites

- Python 3.11 or later (`tomllib` is used; no additional Python packages).
- Installed Lean **4.30.0**, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, including Lake. Install/provide it separately before invoking the build; this package does not install a toolchain.
- An existing Mathlib checkout for revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`, its exact `lake-manifest.json` dependencies in `UPSTREAM_LOCK.json`, and their existing compiled caches.

Keep these dependencies outside the core directory. No copied `.lake` tree or old project `.olean` bank is needed in the distributable source package. Installed upstream caches are an explicit trust boundary.

## Configure a copied core directory

For a normal Mathlib checkout with its dependencies under its own `.lake/packages`:

```text
python configure.py --mathlib /path/to/mathlib
lake build
```

For a parent project where Mathlib and its dependencies are siblings:

```text
python configure.py --mathlib /path/to/packages/mathlib --packages-root /path/to/packages
lake build
```

Quote paths containing spaces. On Windows, paths such as `C:/local/packages/mathlib` are accepted. The distributed package contains no required username or original workspace path. The original workspace's existing relative configuration can remain in use without running this helper there.

`configure.py` validates all inputs before replacing only this copied directory's `lakefile.toml`, `lake-manifest.json` and `LOCAL_CONFIGURATION.json`. It preserves the existing Lean library declarations and changes the Mathlib requirement to a local path. All nine dependency manifest entries become local paths. It does not modify the supplied checkouts, run Git, run Lake, compile Lean files, fetch packages or perform network requests.

`LOCAL_CONFIGURATION.json` contains machine-local paths and is not a proof receipt. Keep it with the local build rather than in the public source release.

The helper checks the core/Mathlib `lean-toolchain` files and matches every Mathlib dependency's pinned revision, URL and config metadata against `UPSTREAM_LOCK.json`. It reads local Git HEAD/ref metadata if present and rejects a different revision. Missing Git metadata is recorded as **revision evidence unavailable**, not accepted as a source-content verification. A matching HEAD also does not establish that the working tree or compiled cache is unchanged.

If a direct installed Lean binary is found under the usual local Elan toolchain directory, the helper runs only that binary's `--version` and requires the exact version/commit. Otherwise the binary check is explicitly recorded as not performed. You can provide it with `--lean /path/to/toolchain/bin/lean` (or `lean.exe`). Do not pass an Elan launcher or shim; automatic toolchain retrieval is outside this helper. The version check does not hash or independently validate the compiler binary.

The subsequent plain `lake build` is the ordinary Lean/Lake route using the local path manifest. Do not run `lake update` or a cache download command as a substitute for installing the pinned prerequisites. Upstream build hooks remain upstream code; configuration alone is not a guarantee about arbitrary hook behavior. Use an offline environment if strict network isolation of the build is required.

## Provenance and licensing

Preserved sources retain their original bytes and notices. `SOURCE_PROVENANCE.json` is an extraction record referencing the original complete audit; it is not a fresh build receipt. New interface files must be distinguished from preserved files in subsequent receipts.

No blanket project-wide license grant has yet been established. Existing Lean/Mathlib notices do not license unrelated local files. The publication attribution/rights review, including the predecessor FLOOR208 materials, remains separate; preserve its explicit scope before redistribution. The proposed license for original contributions is Apache-2.0, subject to an authorized and accurately scoped grant. Do not relabel unidentified third-party expression.

This library and the finite floor38 result make no claim to prove unrestricted Erdős 993, a ceiling theorem or higher unaccepted finite floors.
