# Artifact identities and download scope

The complete source archive and the reusable core source archive are separate. Download the exact named assets attached to the versioned release. GitHub's automatic repository-source download contains the repository at the tag and does not automatically include the large attached certificate archive.

| Source asset | Bytes | Entries | SHA-256 |
|---|---:|---:|---|
| `floor38_unconditional_lean_sources_2026-09-28.zip` | 597,672,786 | 17,501 | `c0d65a24e6eb5fbe09f4ee3d00a1283dbc72a458429c5c6bd5486abc66e65960` |
| `forest_core_sources_2026-09-28.zip` | 232,090 | 125 | `aa45d78b2e4f2130af21baaa09ad40fd0c8ae0bda528347561f655d41a1a02b4` |

The large asset contains exact audited Lean sources and embedded data, locks, native proof/checker helpers, the portable runner, explanation and preserved notices. Its conventional final-source alternative is separately labeled and was not compiled by the native audit. It does not bundle the installed upstream caches or a production object tree.

The small asset contains the reusable general library and interfaces, local dependency configuration, source manifest and public ordinary-build evidence summary. It does not contain the full finite certificate bank. Every distributed Lean source matches its successful ordinary core build. Package checks are distinct from compilation.

## Proof/evidence identities

| Evidence or compiled object | SHA-256 |
|---|---|
| Original complete final proof audit | `323a4c545e6867718d24d2fc0f6f0002497d65f7d1ec70b2a1842f78ae2414e9` |
| Original saved finite-theorem object | `36fe469430177481fd6a79ec88b200a2b3dfa4b210ad33fa2aac4769d7c2d203` |
| Ordinary 116-module core build receipt | `56fea78ce19890163c4baeab961127f8bd615c5332f0d1b68b7d9b3f9e5b8fa4` |
| Concrete Mathlib corollary final receipt | `aae0156a1c6d8c3075d0844d8e178e20c10d4e0dfd8e6f27f4039ca9adeabfa3` |
| Saved Mathlib corollary object | `b6095b384e72725e98dd74fca15ced81e6a834c3fb615237924754f25ea826df` |

These object hashes identify the checked original artifacts; they are not a claim that all objects are bundled in the source ZIPs. Public evidence summaries derive from the recorded original receipts and use relative source paths. They are not invented fresh compiler receipts. Private receipt paths and original command records remain outside the public documentation.

The large archive's public source manifest was created before the subsequent packaging check; a source-stage status field is a snapshot of that stage. The separate completed packaging evidence supplies byte-selection and compressed-entry read-back results. Neither stage asserts a new full proof rebuild.

The author and publication maintainer is Rich Patterson. The repository is [RichP0123/erdos993-floor38](https://github.com/RichP0123/erdos993-floor38), and the versioned release is [`v0.1.0-floor38`](https://github.com/RichP0123/erdos993-floor38/releases/tag/v0.1.0-floor38), dated 29 September 2026. Download the paper, both source archives, their checksum files, and the accompanying `LICENSE`, `LICENSE_SCOPE.md` and `NOTICE.md` from that release. The license documents apply the dated original-contribution grant without modifying either archive. `SHA256SUMS` identifies all six primary assets; individual `.sha256` files additionally identify each source ZIP.
