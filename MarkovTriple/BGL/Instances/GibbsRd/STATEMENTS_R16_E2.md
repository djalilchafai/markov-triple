# STATEMENTS R16 E2 (Armstrong method): weak Caccioppoli (E1) and interior H^2 regularity (E2), written BEFORE the proofs

Namespace `MarkovTriple.BGL.Instances.GibbsRd`; files `EllipticE1.lean`, `EllipticE2*.lean`, (E3 `EllipticE3*.lean` only if capacity).
Textbook: Evans PDE §6.3.1 Thm 1 (interior H^2 regularity, Steps 1-3), Gilbarg–Trudinger Thm 8.8.  `d` arbitrary (d = 0: all sums empty, ℝ^0 a point).
Common hypotheses ("H"): `E : EllData d`; `u h : Rd d → ℝ`, `g : Fin d → Rd d → ℝ`;
  `LocL2 u`, `∀ i, WeakDeriv u (g i) i`, `∀ i, LocL2 (g i)`, `LocL2 h`, `E.VeryWeakSol u h`
  (i.e. `∀ a ∈ A₀ d, ∫ u · E.L a · w = ∫ h · a · w`, the `EllReg`/`resolvent_weak` equation with Z⁻¹ removed).
  Test-function class for `WeakDeriv`: C^∞ compactly supported (Mathlib `∞`, erratum R16-E1).

## E1  `EllData.weak_caccioppoli`  (Evans §6.3.1 Thm 1 Step 1 / (8.28) of G–T; the weak version)
H, `ζ` with `Sm ζ`, `HasCompactSupport ζ` ⇒
  `∫ w · (ζ² · Σᵢⱼ aᵢⱼ gᵢ gⱼ) ≤ −2 ∫ h · (ζ² u) · w + 4 ∫ w · (u² · Γ(ζ,ζ))`.
(Proof by `weakForm_extend` with `v = ζ²u`, `vⱼ = ζ² gⱼ + 2ζ ∂ⱼζ u`.)

## E2  `EllData.interior_H2`  (Evans §6.3.1 Thm 1)
H ⇒ `∀ i, ∃ gi', ... ` precisely: `∀ i j, ∃ G, LocL2 G ∧ WeakDeriv (g i) G j`, i.e. every `∂ᵢu` has a weak derivative in
`L²_loc` in every direction (u ∈ H²_loc).  Consequently (`interior_H2_sobolev`): `Sobolev 2 u`.
Intermediate target (the heart, Evans (Step 2) estimate): for compact `K` there is `C ≥ 0` with
`∀ t, 0 < |t| ≤ 1, ∀ i k: ∫_K (dq k t (g i))² ≤ C`, obtained from the weak form with the test function `v = −D_{−t}(ζ² D_t u)`
(here `v = dq k (−t) (ζ² · dq k t u)`), the difference-quotient Leibniz rule, local ellipticity (`local_ellipticity`), Young absorption,
`eLpNorm_dq_le` and `dq_local_bound`; constants independent of `t`.  Conclusion by `weakDeriv_of_local_dq`.

## E3 (Evans §6.3.1 Thm 2) — only if capacity remains; statement to be fixed below before proof.
