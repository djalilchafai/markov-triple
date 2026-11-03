# AUDIT R16 SOB (self-attack, Armstrong step b)

Scope: `GibbsRd/Sob{Defs,Orthant,Weak,Mollify,Conv,Core,Cm,Main}.lean`, `AxiomCheckR16Sob.lean`.

1. **Vacuity of `WeakDeriv` (`⊤` = ω).**  The prescribed text `ContDiff ℝ ⊤ φ` is analytic in this Mathlib, forcing `φ = 0`
   and making every `g` a weak derivative of every `f`.  Fixed to `ContDiff ℝ ∞` (`((⊤:ℕ∞):WithTop ℕ∞)`) (erratum R16-Sob-E1);
   every smoothness in the files uses `∞` or a numeral cast; the conclusion of `smooth_of_weak_all_orders` is
   `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`.  Non-vacuity is not itself proved by a Lean witness (e.g. `f` smooth ⇒ classical `∂_i f` is the
   weak derivative); not needed for the proofs, but a gap in the self-audit.
2. **Vacuity of "all weak derivatives in `L²_loc`".**  Satisfied by every `C^∞` function, so the hypothesis is non-vacuous;
   `HasSobL1/2` are satisfiable (e.g. `f = 0`; `g = 0` is a weak derivative of `0`).  Not a proof, informal.
3. **Iterated vs multi-index.**  `HasSobL2 (k+1) f` = `L²_loc` and for EVERY direction `i` some `g` (weak `∂_i f`) with `HasSobL2 k g`.
   Equivalent to existence of all words of length `≤ k`; weak derivatives are unique a.e. (not proved here; not needed: the proofs
   only use existence along the word `(0,…,d-1)` and `i`-chains).  Choice of `g` per `i` is by `∃`, so no consistency issue.
4. **Representatives vs a.e.**  Conclusion `∃ g, ContDiff g ∧ f =ᵐ g` (Lebesgue); uniqueness of continuous representatives is
   `Continuous.ae_eq_iff_eq` (used in `smooth_of_weak_all_orders_L1`).  `WeakDeriv` is invariant under a.e. changes, but congruence is not
   stated as a lemma (not needed).
5. **d = 0.**  `Fin 0 → ℝ` is a point with `volume = dirac`; `abs_le_integral_mixD 0` proved; everything is stated for general `d`
   including `0` and `1` (no special casing).  No analytic content for `d = 0`.
6. **Local vs global integrability.**  Hypotheses are local (`LocallyIntegrable`, `LocL2` via compact sets); compactly supported
   cutoffs `χ_R f` are produced by `HasSobL1.mul_smooth`, and a.e. support of weak derivatives is derived (`WeakDeriv.ae_zero_of_open`).
7. **Scope deviation (candid).**  Order `m + d` (mixed `W^{d,1} ⊂ L^∞`), NOT the sharp `m + ⌊d/2⌋ + 1`.  The `L¹_loc` hypothesis is
   weaker than `L²_loc` (so the statements are stronger in the integrability but weaker in the derivative order).  The core interface
   (all orders) is unaffected; for the glue `EllReg` has `∃ n` depending on `m`, so `2n ≥ m + d` suffices.
8. **Mollifier approximation identity** `‖G⋆ρ_n − G‖_{L¹} → 0` is proved here (Scheffé via Lebesgue differentiation), not cited.

## Attack surface (for the hostile auditor)
* A1. `WeakDeriv` text equals the shared one except `⊤ ↦ ∞`; check `∞` is `((⊤:ℕ∞):WithTop ℕ∞)` (`open scoped ContDiff`).
* A2. `HasSobL2/L1` recursion and its equivalence with "all multi-indices" (existence direction only used; a.e. uniqueness not formalised).
* A3. `LocL2` uses `MemLp f 2 (volume.restrict K)` for compact `K` (includes a.e. strong measurability).
* A4. Is `iterD (finRange d)` really `∂_0∂_1⋯∂_{d-1}` and `WeakIter` the matching chain (order of directions irrelevant for smooth `φ`, relevant for weak chain: it is built from `exists_weakIter`, so any order works because `HasSobL1` gives every direction at every level).
* A5. `cutoff R` uses `ContDiffBump` radii `R+1, R+2` (`=1` on `‖x‖ ≤ R+1`), compact support.
* A6. The Sobolev sup-inequality `abs_le_integral_mixD` (Fubini via `volume_preserving_piFinSuccAbove`, `Fin.cons` slicing).
* A7. Statement `sob_contDiff_rep` index `m + d`; `m : ℕ` cast `(m : WithTop ℕ∞)` (finite `C^m`, not `ω`).
* A8. No Lean witness that `WeakDeriv` is non-vacuous (see 1).
