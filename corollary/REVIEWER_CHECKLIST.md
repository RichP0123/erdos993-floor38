# Technical review checklist

The completed local result concerns forests through 37 vertices. No arbitrary
order or ceiling result follows from this package.

1. Run `python tools/verify_corollary_sources.py` from the repository root.
   Confirm the seven Lean source hashes and review the public evidence summary.
   Source integrity is separate from proof compilation.
2. Inspect `Graph`, `AcyclicBridge` and `CountingBridge`. The graph has symmetric,
   irreflexive adjacency; the cycle equivalence covers disconnected forests;
   coefficient equality counts every independent set of the requested rank
   exactly once.
3. Inspect `Transfer.transfer_forest_bound`: its finite-bound input remains an
   explicit premise. The arbitrary finite vertex type is relabelled by an
   equivalence with `Fin`, preserving acyclicity and all coefficient counts.
4. Inspect `MathlibFloor38Target`. Its definition is a literal proposition,
   not an axiom. Its helper retains the original-bound premise, to be discharged
   only by the native application. The final result quantifies over arbitrary
   universes and uses actual `SimpleGraph.indepSetFinset` cardinalities.
5. Inspect the native application: the original input must be a theorem with
   the exact unconditional original signature. The ordinary helper is applied
   to that constant, then `Kernel.Environment.addDecl` checks against the target
   definition's value with `debug.skipKernelTC=false`.
6. Require `NEGATIVE_CONTROL_REJECTED`, `KERNEL_CHECK_ACCEPTED`,
   `EXACT_UNCONDITIONAL_MATHLIB_FLOOR38_SIGNATURE_ACCEPTED`, and
   `SERIALIZATION_END` in assembly and reimport logs. Reimport additionally
   requires `REIMPORTED_THEOREM_KIND theorem`, literal type/universe equality,
   and a checked alias of the actual saved object.
7. Require original-constant identity/ownership, global new-name freshness and
   theorem axiom-cache/body-closure guards. The only permitted axiom names are
   `propext`, `Classical.choice`, and `Quot.sound`; reject `sorryAx` and every
   additional axiom.
8. Require the enlarged whole-import-union compatibility success marker and
   both its incompatible-duplicate rejection and deliberate hash-collision
   controls. The completed local union contained 22,603 modules and 8,327,983 kernel
   constants, with 385 compatible same-name duplicates and zero conflicts.
9. Distinguish proof scopes: ordinary reusable core, the full finite original
   proof, and the applied Mathlib corollary. Do not replace the full proof's
   `ForestStatements` object with an independently rebuilt core object merely
   because their source text agrees. New bridge objects must be compiled
   against the same foundation used by the original theorem.
10. Treat installed pinned Lean/Mathlib compiled libraries as the documented
    upstream software boundary. The public evidence summary inherits the
    completed original corpus audit; it does not claim a new whole-corpus
    rehash. Neither the full exported portable rebuild nor the public manual
    corollary procedure has been exercised end to end.
