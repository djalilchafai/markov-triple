# Hostile audit: round 16, exact kernel semigroup via the Feller property (branch a84a763)

Independent auditor. **Result: no soundness defect, misformalization or vacuity.** `IsFeller` (a.e. form via `clsC`) is equivalent to P_t C(X) ⊂ C(X) under full support; `clsC_injective` correct;
`fellerKernel_add` is a genuine consequence (Riesz measure pinned down by `integral_fellerMeasure`; CK via `Kernel.integral_comp`, `integral_fellerKernel`, `fellerOp_add_time`, `measure_ext_C`); `isFeller_of_dense`,
`integral_semigroup_eq`, `fellerKernel_bind`, `fellerKernel_rep`, `fellerKernel_unique`, `circle_fellerKernel_eq` (every x) re-derived; instances (F),(S),(C) verified for the circle and the zonal S^3.
Structural: frozen OK; lakefile/manifest/toolchain unchanged; 5 modules recompiled from scratch, 30 axiom lines standard.
Findings: (1) `set_option linter.unusedSectionVars false` in four new files suppressed warnings: REMOVED, 15 resulting warnings fixed with `omit … in`; (2) 'cannot be obtained by textbook arguments' (Route B) softened to 'does not give exactness at all x without Feller/regularity';
(3) cosmetic headers. Open (ERRATA R16-2): no exact kernel semigroup without Feller; no non-compact extension; no joint measurability in t (so no `MarkovProcessBridge` for these kernels); Feller not automatic.
