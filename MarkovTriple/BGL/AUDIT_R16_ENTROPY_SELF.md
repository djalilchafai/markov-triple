# Round 16 "Entropy": self-audit (Armstrong step b/c)

Targets: `MarkovTriple/BGL/Theory/Interp/STATEMENTS_R16_Entropy.md`.  Frozen `EntropyInterpolation`, `FiniteDimInterpolation` untouched.

## 1. What was proved (all `#print axioms` = propext, Classical.choice, Quot.sound; `Theory/Interp/EntropyAxiomCheck.lean`)
* `FullTriple.entropyInterpolation (T) (hCD : T.CD ρ n) (hρ : 0 ≤ ρ) [IsFiniteMeasure T.μ] : T.EntropyInterpolation` (all four fields).
* Consequences: `logSobolev_unconditional`, `logSobolev_domain_unconditional` (any `FullTriple`, probability measure, `CD(ρ,n)`, `ρ>0`),
  `GibbsData.gibbsFull_logSobolev_unconditional` (`V'' ≥ ρ > 0`), `finiteDim_bdd` (field `bdd`), reductions `finiteDimInterpolation_of_ext`,
  `logSobolev_dim_of_ext`.
* Pipeline (book route, Prop 5.5.3 / 5.7.1): `s ↦ P_sφ` is `L²`-differentiable (Interp `hasDerivAt_orb`); `e(s) = ∫Θ(ε+P_sφ)` (`Θ` smooth cutoff of `x log x`),
  chain rule `hasDerivAt_integral_smooth`, Green `ibp_bdd` ⇒ `e' = -I`; `I(s) = -∫Λ(g_s) L P_sφ` (Green) ⇒ `I'` by `Compact.hasDerivAt_pairS`
  (generic finite `μ`) `= -(∫Λ'(g)(LP)² + ∫Λ(g) LLP)`; `fisher_alg` identifies this with `-2∫gΓ₂(Λ∘g)` using four Green formulas
  (test functions `Λ(g)`, `Λ'(g)`, `X = Γ(P)`, `Q·Λ'(g)`), the `Γ₂` chain rule `Γ₂_comp` (derived from the definition, `ψ'''` cancels), and
  `Γ(Γ P) ≤ 4(Γ₂-ρΓ)Γ` (`reinforced_cd`, BGL (3.3.6)) to put `X ∈ 𝒟(ℰ)`.

## 2. Attacks on the statements
1. **Vacuity / unsatisfiable hypotheses.**  Hypotheses: `IsFiniteMeasure`, `CD ρ n`, `0 ≤ ρ`.  All are satisfiable (compact triples, OU, Gibbs with `V'' ≥ ρ ≥ 0`
   exist and are used: `gibbsFull_logSobolev_unconditional`).  No `BddGamma`-type hypothesis remains (ERRATA R16-E1): `A₀` is bounded by the field `DiffusionTriple.bounded` (D2).
   If a reader insists the book's `𝒜₀ ⊂ L^p` only (unbounded elements allowed), D2 is stronger than the book, but D2 is a frozen field of the library, not introduced here.
2. **`ρ < 0`.**  Not claimed (`0 ≤ ρ` is a hypothesis of `entropyInterpolation`): the bound `Γ(P_tφ) ≤ B` uses Thm 3.3.18, which requires `ρ ≥ 0`.  Note `CD(ρ,n)` with `ρ<0` would need
   the error-term analysis flagged in GAPS (R15).
3. **Infinite `μ` vs probability.**  `[IsFiniteMeasure T.μ]` is used for `L²⊂L¹`, `Lp`-valued constants and `∫ g log g`.  For infinite `μ` and `ε ≠ 1` the integrand `g log g` is not integrable
   (`ε log ε ≠ 0` constant part), so `entE` is the junk value `0` and `hasDerivAt_E` would fail whenever `I>0`; hence finiteness is necessary for the frozen structure, not a convenience.
   The LSI statements add `IsProbabilityMeasure` (mean value `m log m`, `ent_le_fisher`).
4. **a.e. conventions.**  `entG φ ε s x = ε + Pt s.toNNReal φ x` uses the fixed `𝒜`-representative `Pt` (`Classical.choose`).  Every identity is a.e.; `entE`, `entI` depend on `Pt` only through its a.e. class
   (`entE_eq`, `entI_eq_quot`, `gcurve_ae`).  For `s ≤ 0` the definition uses `Pt 0`; continuity on `Ici 0` is proved on all of `ℝ` (the curves `orb`, `cK` are continuous on `ℝ`).
5. **ε-regularisation / integrability of `1/g`.**  `g ≥ ε` a.e. (`gcurve_ge`, `Pt_nonneg`), `1/g ≤ 1/ε`.  The cutoffs `Θ, Λ` of the frozen field are arbitrary `BE.Cut ε M`; the proof only uses that
   `Λ^{(k)}(ε+y)` (k ≤ 3) are bounded smooth and equal `log^{(k)}` on `[0,M]` (`Lam.values`, via `C.hΛeq` eventually-equal, hence valid for any cut).
6. **Dead / unused material.**  `hasDerivAt_integral_div`, `hasDerivAt_integral_smooth` (the latter used), `ibp_Pt_comp`'s general `Ψ`: `hasDerivAt_integral_div` is proved but not on the final path (route changed, R16-E1).
7. **Dependence on other stages.**  `Compact.hasDerivAt_pairS` (Theory/Compact/Entropy.lean, generic over finite `μ`), `strong_gradient_bound_unconditional` (Interp), `integrable_Γ₂_of_domain` (Prop 3.3.17 forward),
   `reinforced_cd`, `ibp_bdd`.  If any of these were wrong, so would this stage; `ibp_bdd` is the Interp-stage lemma flagged in its own audit §5.4.

## 3. Deviations from the book (candid)
* The book's proof of Prop 5.7.1 only says "`P_t f` is in `𝒜` and bounded together with `Γ(P_tf)`, `LP_tf`" and differentiates under the integral; all differentiations here are
  made explicit in `L²`/`L¹` (the `Θ`, `Λ` cutoffs are needed since `x log x` is not globally smooth).
* `I' = -2J` is not proved by differentiating `∫Γ(g)/g` directly (needs `Γ(g)` in `L²`-pairings); it is proved from `I = -∫Λ(g)Lg` (Green) and the `L²`-product rule, then the algebra of `fisher_alg`.
  This uses Green's formula `∫ g L Y = ∫ Y L g` for `Y` in `𝒟(ℰ)` bounded with `LY ∈ L¹` — in the book that is Prop 3.3.17/3.3.6 "by the analysis of Sect. 3.3"; here via `ibp_bdd` (density + truncation, Interp stage).
* `ρ ≥ 0` is an assumption of the discharge; the book's Thm 5.7.4/Prop 5.7.1 only need `ρ > 0` anyway.

## 4. Not done (exact)
* **`FiniteDimInterpolation.ext`** (BGL p. 272: "by Prop 3.3.6 and Lemma 3.3.16, (5.7.12) extends to bounded `f ∈ 𝒜` with `Γ(f)`, `Lf` bounded"): the frozen field is for ARBITRARY `f ∈ 𝒜` with `ε ≤ f ≤ ε+M`, `Γ(f)`, `|Lf| ≤ B`, and the two integrability hypotheses only.  Obstacles:
  (i) `f ∈ 𝒟(L)` must be derived from `f ∈ 𝒜`, `Lf ∈ L²` (self-adjointness + F7 gives it, not formalised here); (ii) the chain (5.7.6)-(5.7.12) in `LogSobolevDimChain.lean` is proved for `g ∈ 𝒜₀` with `e^{g/2} ∈ 𝒜₀` and uses `∫Γ₂(h)=∫(Lh)²` and F7 with test functions in `𝒜₀`; redoing it with bounded `𝒜`-functions needs `Green` (`ibp_gen`) for `e^g`, `e^{g/2}`, `Γ(g)` etc. and domain/`Γ`-integrability facts as in `fisher_alg` (same technique, an estimated 400+ more lines); (iii) no non-book idea was identified.
  Consequently the finite-`n` constant `(n-1)/(ρ n)` for non-compact triples is available only as `logSobolev_dim_of_ext` (hypothesis = exactly `ext`).
* `ρ < 0`; infinite `μ`.

## 5. Attack surface for the independent hostile audit
1. `hasDerivAt_integral_smooth` / `cs_facts` (EntropyAnalysis): the constants and the MVT step (`K2 (b-a)^2`); `continuous_integral_smooth` uses `integral_abs_le` (sign function, `oneNorm`).
2. `tendsto_inv_diff`, `slope_bound`, `hasDerivAt_integral_div` (EntropyQuot): the choice of truncation level `N`, pointwise inequalities `inv_diff_le`; only `continuous_integral_div` is used downstream.
3. `integral_dTheta` (EntropyDeBruijn): `ibp_bdd` hypotheses (`hQG` proof-irrelevance `Pt_mem_Q` vs `hG2.toLp`), `k = Λ+1`, `Θ' = Λ+1` on the range, sign of `-I`.
4. `entI_eq_neg_pair`, `hasDerivAt_entI_pair` (EntropyFisher): the orb/gcurve ae identifications; use of `Compact.hasDerivAt_pairS` with `Bdd`.
5. `Γ_Pt_bdd`: uses `exp(-ρ t) ≤ 1` for `ρ ≥ 0` and `|P_t √Γφ| ≤ √C`.
6. `Γ₂_comp` (EntropyChain): final `ring` after rewriting with `E1`,`E2` (`ψ'''` cancellation); a wrong coefficient would be caught only by that `ring`.
7. `fisher_alg` (EntropyIdentity): the hypothesis bundle `FisherHyp`; the relations `R_a,R_b,R_c,R_d,R_e` and the final `linarith`; the pointwise identity `pw` (uses `Lam.values`).
8. `fisherHyp` (EntropyMain): `ΓQ` via `ΓA_congr_A`, `LQ` via `L_congr_A` + `memLp_L_Pt (Lt φ)`; `Γ₂` integrability via `integrable_Γ₂_of_domain` (needs `CD`).
9. Frozen-structure matching: `hasDerivAt_entI` states exactly the third conjunct with `entJ C.Λ φ ε s` (unfolded `simp only [lam0, entG]` conversion); `entropyInterpolation` fields use `_` for unused `ε,M,s`.
10. `finiteDim_bdd`: `L(ε+P) = L P` a.e. via `L_lin`, `L_const`.
