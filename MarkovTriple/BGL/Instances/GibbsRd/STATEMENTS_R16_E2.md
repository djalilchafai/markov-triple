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

## Status at the end of the batch (appended after the proofs; the targets above are unchanged)
PROVED (Lean, 0 sorry, axioms propext/choice/Quot.sound, `AxiomCheckR16E2.lean`):
* E1 `EllData.weak_caccioppoli` (`EllipticE1.lean`), exactly the displayed statement.
* E2 `EllData.interior_H2` and `EllData.interior_H2_sobolev` (`EllipticE2E.lean`), exactly the displayed statements.  The "intermediate target"
  was proved in the equivalent form `EllData.energy_bound`: `∃ C ≥ 0, ∀ |t| ≤ 1, ∫ ζ² Σⱼ (D_t gⱼ)² ≤ C` (the L²(K) bound on `K ⊂ {ζ = 1}`
  is then extracted inside `interior_H2` via `eLpNorm_le_of_sq`).  Pieces: `dq_identity` (`EllipticE2B`), `pw_main`, `pw_R2`,
  `qf_young`, `final_arith` (`EllipticE2C`), `energy_step` (`EllipticE2D`, all constants explicit via `Cbound`), `locL2_dq`, `sq_integral_eq` (`EllipticE2A`).
NOT DONE: E3 (higher regularity); the `L²_loc ⇒ H¹_loc` Friedrichs step; hence still no `interior_regularity_step`; no link of `VeryWeakSol` to `EllReg` here.
Plan for E3 (fixed, not claimed): for `k`-th derivative `g_k = ∂_k u ∈ H¹_loc` (from `interior_H2`) show `VeryWeakSol (g k) h'` with
`w h' = ∂_k(h w) − Σᵢⱼ ∂ⱼ(∂_kAᵢⱼ gᵢ)` (Aᵢⱼ = w aᵢⱼ), by `∂_k(w L a) = w L(∂_k a) + div(∂_kA ∇a)`, two weak integrations by parts
(`WeakDeriv` of `u` and of `gᵢ`), `h' ∈ L²_loc` by `Sobolev.smooth_mul`; apply `interior_H2` to `g k`; induct on `k` generalising over `u`.
