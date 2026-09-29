# Reproduction

There are two source packages with different purposes. The small core was built through ordinary Lake; it contains reusable mathematics and interfaces. The complete finite proof additionally needs the rooted-state and interval-certificate corpus. A successful small-core build does not substitute for that corpus.

## Pinned prerequisites

Use Python 3.11 or later and an existing Lean 4.30.0 installation at commit `d024af099ca4bf2c86f649261ebf59565dc8c622`. Supply an existing Mathlib checkout at `c5ea00351c28e24afc9f0f84379aa41082b1188f` and the exact package revisions in the supplied lock, with their compiled caches available. The supplied workflows do not install or download those prerequisites.

Installed upstream caches remain an explicit trust boundary. A local path, matching lock or checkout HEAD is not by itself verification of working-tree or cache contents. Record the actual dependencies used for a new reproduction.

## Small general library: ordinary build

Work in the repository's [core directory](../core/README.md), or extract `forest_core_sources_2026-09-28.zip` into a new directory. For Mathlib with its dependencies under its own `.lake/packages`:

```text
python configure.py --mathlib /path/to/mathlib
lake build
```

If Mathlib and the other dependencies are siblings:

```text
python configure.py --mathlib /path/to/packages/mathlib --packages-root /path/to/packages
lake build
```

Quote paths containing spaces. Configuration preserves the library declarations and produces local-path Lake requirements. It checks toolchain files and dependency-lock metadata; it checks available local HEAD metadata without running Git. It may run a direct installed Lean binary's `--version`, recording when that check is unavailable. An explicit direct executable can be supplied with `--lean`; Elan launcher directories are rejected. Configuration performs no compilation or package download.

The resulting `LOCAL_CONFIGURATION.json` contains machine-local paths and is not a compiler receipt. Keep it with the local reproduction record. Do not publish it as a proof certificate.

The original ordinary core build compiled 116 project modules in a fresh directory without copied project objects, using installed locked upstream caches. The source package's read-back and clean configuration checks also passed; those latter checks were not another Lean compilation. Upstream build hooks remain upstream code, so strict network isolation of a new build should be enforced by its execution environment.

The core exposes graph/counting and acyclicity correspondences, transfer to arbitrary finite vertex types, sequence equivalences and general certificate reasoning. Its generic transfer theorem accepts a finite bound as an explicit input. The concrete bound itself belongs to the separately verified full theorem/application evidence.

## Complete finite proof

Extract `floor38_unconditional_lean_sources_2026-09-28.zip` and follow its detailed `REPRODUCTION.md`. Its public manifest records the complete selected source closure, embedded data and exact locks. Ordinary proof modules are under `src/`; native helpers are under `tools/`; the distinct conventional final alternative is under `standard/`.

```text
python portable_build_floor38.py
python portable_build_floor38.py --execute --mode native --toolchain /path/to/lean-toolchain --mathlib-project /path/to/mathlib-project
```

The first command validates and prints a plan. The second rebuilds the project dependencies, then runs custom kernel assembly, fresh custom-loader final-object reimport and full-import compatibility checks. It writes new outputs and receipts separately. `--resume` reuses only appropriately matching outputs from that portable workflow.

A complete new execution of this exported-source workflow has **not** been completed. The accepted original theorem is supported by its actual prior dependency builds and final audit, not by a claimed fresh portable run. Its optional ordinary `--mode standard` final source is also uncompiled in that audit and differs from the native output by an extra bank definition. Do not associate the native object's successful receipt with that alternative source.

The concrete Mathlib corollary has separately checked bridges and final custom application/reimport evidence. The small library alone does not reconstruct that saved final object. Its exact target, method and artifact identity are recorded in [VERIFICATION.md](VERIFICATION.md) and [ARTIFACTS.md](ARTIFACTS.md).

## Resources and reporting

The complete source archive is about 570 MiB compressed and 3.27 GiB uncompressed. The historical compiled import inventory exceeded 89 billion bytes. Large ordinary dependency builds exceeded 6 GiB private memory; one order-36 attempt reached about 7.14 GiB before an 8 GiB-cap retry. The optimized native final assembly fit below 1 GiB private memory. These are different stages and must not be conflated.

No full portable build time or disk guarantee is available. The optional process-tree memory monitor is a sampled soft limit, not a hard OS job/cgroup cap. It cannot guarantee capture of every transient spike or detached child.

For a reproduction report, provide exact package/toolchain identities, target, command, source version, exit status and relevant logs, with private paths removed from any public copy. Distinguish a dependency/configuration/resource failure from a rejected proof, and distinguish a successful core build from a full finite-proof rebuild.
