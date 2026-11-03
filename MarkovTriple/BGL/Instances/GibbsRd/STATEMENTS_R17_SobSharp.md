# STATEMENTS R17 SobSharp (Armstrong method): sharp Sobolev embedding `H^k_loc ⊂ C^m` for `k > m + d/2` — written BEFORE the proofs

Textbook references: Evans PDE §5.6.3 Thm 6 / §5.8.1; Gilbarg–Trudinger Thm 7.26; Folland, *Real Analysis*, Thm 9.17 (Sobolev
embedding `H^s ⊂ C^m` for `s > m + d/2`, proved by Plancherel + Cauchy–Schwarz on `∫ (1+|ξ|)^m |f̂|`).  BGL (Bakry–Gentil–Ledoux)
only *cites* the interior elliptic regularity / Sobolev embedding (Appendix A, "Sobolev spaces", and the discussion after
Def. 3.3.8) without proof; the Fourier (Plancherel) route is the textbook one for the index `k > m + d/2`.
Namespace `MarkovTriple.BGL.Instances.GibbsRd.Sob`; files `SobSharp*.lean`, `EllRegSharp.lean`.  Existing definitions
(`WeakDeriv`, `LocL2`, `HasSobL2`, `HasSobL1`) are reused unchanged; existing theorems (`sob_contDiff_rep`, `ellReg`, …) are untouched.

## Theorems (all for `f : (Fin d → ℝ) → ℝ`, Lebesgue measure)
* S1 `sob_contDiff_rep_sharp (m k : ℕ) (hk : d + 2 * m < 2 * k) (hf : HasSobL2 k f) :
     ∃ g, ContDiff ℝ (m : WithTop ℕ∞) g ∧ f =ᵐ[volume] g`        (condition `k > m + d/2`, real-number form `d/2 + m < k`).
* S1' `sob_contDiff_rep_sharp' (m) (hf : HasSobL2 (m + d / 2 + 1) f) : …` (nat form `k = m + ⌊d/2⌋ + 1`, equivalent minimal order).
* S2 `sob_continuous_rep_sharp (hf : HasSobL2 (d / 2 + 1) f) : ∃ g, Continuous g ∧ f =ᵐ g`.
* S3 `smooth_of_weak_all_orders_sharp` : same conclusion as `smooth_of_weak_all_orders` (`ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)`, NOT `⊤ = ω`),
  obtained from S1.
* S4 (chain) `EllData.ellReg_sharp : ∀ m, ∃ n, n = m + d / 2 + 1 ∧ (EllReg-style statement with this `n`)`, i.e. the elliptic chain `E1/E2/E3`
  closes with chain length `m + ⌊d/2⌋ + 1` (instead of `m + d`).  `EllData.EllReg` (existing statement) is unchanged and `ellReg` is unchanged.

## Proof route (no sorry, no new axiom)
Compactly supported `F` with `HasSobL2 k F`:  mollify `F_n = F ⋆ ρ_n` (existing `mol`, `rho`); `F_n ∈ C_c^∞ ⊂ 𝓢(E)`, `E = EuclideanSpace ℝ (Fin d)`;
Plancherel for Schwartz functions (Mathlib `SchwartzMap.integral_norm_sq_fourier`) and `𝓕(∂_i ψ) = 2πi ξ_i 𝓕ψ` give
`∫ (1 + Σ_i (2π ξ_i)^{2k}) |F̂_n|² = ‖F_n‖₂² + Σ_i ‖∂_i^k F_n‖₂² ≤ ‖F‖₂² + Σ_i ‖∂_i^k F‖₂²` (mollification is an `L²` contraction,
`∂_i^k F_n = (∂_i^k F) ⋆ ρ_n` by the existing `iterD_mol`); `F̂_n = F̂ ρ̂_n → F̂` pointwise (`|ρ̂_n| ≤ 1`), Fatou gives the same bound for `F̂`;
Cauchy–Schwarz/AM-GM with `∫ (1+|ξ|)^{-2(k-m)} < ∞ ⇔ 2(k-m) > d` (Mathlib `integrable_one_add_norm`) gives `(1+|ξ|)^m F̂ ∈ L¹`, hence
`g = 𝓕⁻ F̂ ∈ C^m` (Mathlib `contDiff_fourier`), and `F_n → g` (dominated convergence) with `F_n → F` a.e. (existing `ae_tendsto_mol`).
Localisation by the existing smooth cutoff (`cutoff`, `exists_rep_of_local`), exactly as in `local_rep`.

## HONEST SCOPE
Target: the full sharp threshold `k > m + d/2` (all `d`).  Not claimed: optimality of the threshold (counterexamples), the Sobolev
embedding for `L^p`, `p ≠ 2`, nor any weighted/global statement.  Nothing downstream is changed (the existing `ellReg` stays as is).

## Status (end of round 17, Lean names; the statements above are unchanged)
All targets proved, no `sorry`, standard axioms only (`AxiomCheckR17SobSharp.lean`).
* S1 `Sob.sob_contDiff_rep_sharp` (`SobSharpMain.lean`); S1' `sob_contDiff_rep_sharp'`; S2 `sob_continuous_rep_sharp`; S3 `smooth_of_weak_all_orders_sharp`.
* Core: `sob_core_sharp` (`SobSharpCore.lean`, compact support), localisation `local_rep_sharp`.
* Ingredients: `integral_sq_mol_le` (L² contraction, `SobSharpML2`), `integral_pow_sq_fourier_lft` (Plancherel + derivatives, `SobSharpFourier`),
  `hat_mol`/`tendsto_hat_mol` (`SobSharpHat`), `wgt_hat_lintegral_le` (Fatou, `SobSharpBound`), `integrable_weighted_hat` (`SobSharpWgt`),
  `HasSobL2.mul_smooth`, `exists_weakIter_L2` (`SobSharpWeak`).
* S4 `EllData.ellReg_sharp_order`, `ellReg_sharp`, `ellReg_of_sharp` (`EllRegSharp.lean`): chain length `m + ⌊d/2⌋ + 1`.
Not done: optimality of the threshold; `L^p`, `p ≠ 2`; the old `ellReg`/`sob_contDiff_rep_L2` are left as they were (their orders `m+d` remain valid, weaker).
