# Unimodality of forest independence polynomials through 37 vertices

**Every finite simple forest with at most 37 vertices has a unimodal independence sequence.** The result has been checked locally with Lean 4.30 and Mathlib. It has no inherited census assumption or unproved certificate premise. This is a finite theorem related to Erdős problem 993; it does not settle the problem for arbitrary orders.

For a graph \(G\), the independence sequence counts independent vertex sets by cardinality. Unimodality allows a plateau at the peak. Empty graphs and disconnected forests are included. “Floor38” means that any counterexample would have at least 38 vertices; it does not assert one exists at 38.

## What is verified

| Result | Completed check |
|---|---|
| Forest unimodality through 37 in the original finite-graph representation | Complete project proof audit, custom final kernel assembly, fresh custom-loader reimport and complete import-union compatibility check |
| General `ForestCore` library | Ordinary `lake build` of all 116 project modules in a fresh source directory, using installed locked upstream caches; no custom assembler or copied project objects |
| Concrete Mathlib statement on arbitrary finite vertex types | Fresh ordinary bridge proofs followed by custom kernel application of the completed finite theorem, export, fresh custom-loader reimport and enlarged import-union compatibility check |

The original theorem is

```lean
Erdos993.Floor216.actual_forest_unimodal_through_thirty_seven :
  ∀ n ≤ 37, ∀ G : Graph n, IsForest G → Unimodal (coefficient G)
```

The separately checked Mathlib corollary is

```lean
Erdos993.ForestCore.mathlib_forest_unimodal_through_thirty_seven :
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    Fintype.card V ≤ 37 → G.IsAcyclic →
      Erdos993.Unimodal (fun k => (G.indepSetFinset k).card)
```

The generic bridge's input bound has been supplied by the completed original theorem; it is not an assumption remaining in this corollary. The only recorded final axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Read and reproduce

- [Proof paper (PDF)](docs/PAPER.pdf) and [editable source](docs/PAPER.md): mathematical argument and formalization details.
- [Verification account](docs/VERIFICATION.md): exact checks, custom-loader method and trust boundary.
- [Reproduction instructions](docs/REPRODUCTION.md): ordinary small-library build versus the complete finite proof.
- [Artifacts and checksums](docs/ARTIFACTS.md): source archives and fixed evidence identities.
- [Attribution](docs/ATTRIBUTION.md), [bibliography](docs/BIBLIOGRAPHY.md) and [BibTeX](docs/references.bib).
- [Reviewer guide](docs/REVIEW.md): focused checks and unresolved reproduction questions.
- [Contributions](CONTRIBUTORS.md), [notices](NOTICE.md) and [license scope](LICENSE_SCOPE.md).
- [Concrete Mathlib corollary sources and reproduction steps](corollary/README.md).

To build the [small library](core/README.md), work in `core/` or extract `forest_core_sources_2026-09-28.zip` into a new directory. Provide an existing pinned Mathlib installation and run:

```text
python configure.py --mathlib /path/to/mathlib
lake build
```

For sibling dependency directories, use `--packages-root /path/to/packages`. The package configures local paths; it does not fetch dependencies. See the reproduction instructions for the exact toolchain and source-integrity limits of configuration checks.

The complete finite proof is a separate, approximately 570 MiB release asset, `floor38_unconditional_lean_sources_2026-09-28.zip`. GitHub's automatically generated repository source ZIP is not a substitute for that attached certificate archive.

## Verification limitations

Both complete final theorem applications and their fresh full-object reimports use the reviewed custom exact loader. A small pilot also passed ordinary Lean reimport. The complete conventional final-source alternative and a fresh full exported-source rebuild have not been completed. The ordinary small-library build does not imply otherwise. Installed locked Lean/Mathlib libraries remain an explicit upstream trust boundary.

A three-axiom printout alone would not establish the claim: statement meaning, actual enabled kernel checks, exact original declarations, dependency provenance and full-import compatibility are also part of the evidence. No independent-machine full reproduction or external human referee endorsement is claimed.

## Credit and publication status

The problem and earlier mathematical/computational work are credited in the paper and bibliography. Development involved substantial generative-AI assistance. The saved prompt, returned reports and acquisition/replay audits trace the certificate method to this project's commissioned FLOOR208 research round. Its individual seat/model identity was not retained. This missing detail does not make the round an unidentified outside source. Original project contributions are licensed under [Apache-2.0](LICENSE), with the exact files, archives and third-party exceptions stated in [LICENSE_SCOPE.md](LICENSE_SCOPE.md). Existing notices are preserved.

The author and publication maintainer is Rich Patterson. The repository is [RichP0123/erdos993-floor38](https://github.com/RichP0123/erdos993-floor38). [Release `v0.1.0-floor38`](https://github.com/RichP0123/erdos993-floor38/releases/tag/v0.1.0-floor38) is dated 29 September 2026. [CITATION.cff](CITATION.cff) supplies the author, version, release date, license and citation links. No ceiling theorem, higher unaccepted finite bound, unrestricted solution or priority claim is made.

## Check the downloaded files

Before configuring local build paths, run `python verify_release.py`. If the named release assets are in another directory, run `python verify_release.py --assets-dir /path/to/assets`. These checks compare file hashes and do not compile Lean. `--require-publishable` additionally rejects unresolved publication metadata and unlisted repository files.

The `.gitattributes` file preserves exact source bytes, including historical line endings. The full source ZIP remains a separate release attachment. The release also supplies `LICENSE`, `LICENSE_SCOPE.md` and `NOTICE.md` alongside both source archives.
