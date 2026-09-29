# Related work and reuse notes

Documentation addendum, 29 September 2026. This page records a focused primary-source inspection completed after the fixed `v0.1.0-floor38` release. It does not change the released paper, proof sources or asset hashes, and is not an independent build or review of another project's full proof.

## Zhang and Li

Tong Zhang and Wei Li, *Unimodality of Forest Independence Polynomials*, version 27 September 2026, [DOI 10.5281/zenodo.22999166](https://doi.org/10.5281/zenodo.22999166). The DOI resolver redirects to Zenodo, and the DataCite record identifies this title, these authors and this version. No unverified arXiv identifier is assigned here.

Their [companion repository at commit `8067893`](https://github.com/zhangzenozhang-jpg/forest-unimodality-arxiv-verification/tree/806789352f7ed8e64594907a2ed334652ce11160) supplies computational verification materials. Its README distinguishes certificate checking from the written reductions and says those reductions have not been formalized there. Proposition 1.2 of their supplied manuscript states unimodality through 60 vertices. Their work is credited for its own mathematics and certificate data; it is not the source of this project's independently developed rooted-tree certificate route.

## Fang, Lu, Nevo, Yao and Zheng

Ethan X. Fang, Junwei Lu, Eran Nevo, Yuan Yao and Hailun Zheng, *Unimodality of Independence Polynomials for Sufficiently Large Forests*, [arXiv:2609.20961v1](https://arxiv.org/abs/2609.20961v1), submitted 17 September 2026.

The [associated Lean development at commit `b2a1d3e`](https://github.com/junwei-lu/Erdos_993_Tree_Independent_Set_Unimodality/tree/b2a1d3ede8aef259b1de6e319e7fd6cb56481ac1) states an absolute threshold above which every forest is unimodal and reports only Lean's three standard axioms. Its reported build was not independently reproduced here. Its existential threshold and this project's finite bound do not by themselves establish that all intermediate orders are covered.

## Vallier's formalization

Kevin Vallier's AI-assisted [erdos993-lean project at commit `865e814`](https://github.com/selfreferencing/erdos993-lean/tree/865e81498ecacda3de0d47647927353a7fadbba5) credits Zhang and Li for the finite-order mathematics and certificates. The inspected source includes [`forest_unimodal_of_card_le_sixty_kernel`](https://github.com/selfreferencing/erdos993-lean/blob/865e81498ecacda3de0d47647927353a7fadbba5/Erdos993Lean/ZhangKernel/Main.lean#L129-L133), stated for actual finite forests through 60. Selected certificate declarations use `decide +kernel`; the final source supplies the certificate and graph-side premises. The README reports 17,100 parameter triples covered by 900 kernel evaluations across 24 check modules, and only `propext`, `Classical.choice` and `Quot.sound` for this finite theorem. Those counts and axiom output were not independently reproduced here.

The repository also contains a full-result theorem using a replacement large-order argument. Its documented `native_decide` route additionally trusts native compilation through `Lean.ofReduceBool` and `Lean.trustCompiler`. That is a different trust boundary, not an unproved mathematical hypothesis or evidence of invalidity. Its authors describe the work as unrefereed. This source inspection neither validates nor refutes the complete result.

The reported through-60 theorem has a stronger numerical range than this project's through-37 theorem. This project offers a separate finite-certificate formalization and reusable mathematics; it makes no strongest-bound, first-formalization or priority claim.

## Reuse and versions

| Project | Pinned Lean version | Pinned Mathlib commit |
|---|---|---|
| ForestCore | `leanprover/lean4:v4.30.0` | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| FLNYZ development | `leanprover/lean4:v4.29.1` | `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| Vallier development | `leanprover/lean4:v4.28.0` | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |

`ForestCore` has an ordinary 116-module Lake build in a fresh project source directory using existing pinned upstream dependencies and caches. Its tested configuration route is described in [the root README](../README.md#read-and-reproduce) and [core instructions](../core/README.md). Porting and rebuilding may be needed to share lemmas with a project using another toolchain. A fresh online dependency bootstrap is not claimed to have been tested.

Potentially reusable components include graph recurrences, coefficient-counting and acyclicity bridges, sequence lemmas and certificate algebra. These are offered for assessment; no claim is made that another project needs them or that they complete its formalization. The full through-37 theorem remains subject to the distinct, explicitly documented [custom-loader and reproduction qualifications](VERIFICATION.md).
