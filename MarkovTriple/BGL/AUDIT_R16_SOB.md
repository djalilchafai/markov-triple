# Hostile audit: round 16, Sobolev embedding in R^d (mixed-derivative route; branch tip bd7c38f)

Independent auditor. **Result: no soundness defect, misformalization or vacuity.** The auditor proved in a scratch file that `WeakDeriv` is the standard weak derivative
(`classical_weak`: smooth f has classical ∂ᵢf as weak derivative, sign and Lebesgue measure confirmed), that `HasSobL1 k f` holds for every smooth f (hypotheses satisfiable, `sob_contDiff_rep` not vacuous),
and that `WeakDeriv` has teeth (`indicator_not_weak`: an indicator has no weak derivative in d=1). All smoothness classes use `((⊤:ℕ∞):WithTop ℕ∞)` (never `ContDiff ℝ ⊤`, which is ω in this Mathlib; the
ω claim itself was inferred from the author's erratum R16-Sob-E1, not tested). Re-derived: `abs_le_integral_mixD` (Fin.cons slicing, FTC, Fubini), `pd_mol_weak` (signs), the Scheffé L¹ convergence of mollifiers,
the uniform-Cauchy argument of `sob_core`, the C^m induction via `hasFDerivAt_of_tendstoUniformly`, the gluing `exists_rep_of_local` and locality. `smooth_of_weak_all_orders` requires all orders and is derived honestly.
Structural: frozen OK; all `Sob*`, `AxiomCheckR16Sob`, `RegReduction` modules recompiled from scratch, 0 errors/warnings; axioms standard.
Findings (documentation only): `WeakDeriv` of the Sobolev files and of the elliptic files are two standalone definitions (identical text; identification deferred to the glue stage); the embedding order is m + d, not the sharp m + ⌊d/2⌋ + 1 (stated honestly, R16-Sob-E2).
