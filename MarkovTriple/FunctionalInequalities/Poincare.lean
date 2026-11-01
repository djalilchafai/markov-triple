import Mathlib
import MarkovTriple.FunctionalInequalities.GapFromSquare
import MarkovTriple.FunctionalInequalities.TripleSquare

/-!
# Phase 4: `CD(ρ,∞)` + ergodicity ⟹ Poincaré inequality `PI(1/ρ)` (Bakry–Émery / Lichnerowicz)

**Route** (the integrated `L²` / spectral route of AUDIT_FROZEN3, Phase 4 to-do, item 4):

1. `∫ L h = 0` for `h ∈ 𝒜₀`, hence `∫ Γ₂(g) = ∫ (L g)²` and, by `CD(ρ,∞)` on `𝒜₀`,
   `ρ ∫ Γ(g) ≤ ∫ (L g)²` (`TripleSquare.lean`).
2. With `R = (1 + B)⁻¹` the Friedrichs resolvent, `B = -L̄`: step 1 reads
   `ρ ⟪w - R w, R w⟫ ≤ ‖w - R w‖²` for `w` in the dense set `(1 - L)𝒜₀` (`esa`), hence for all `w`
   by continuity (`square_all`).
3. Abstract Hilbert lemma (`gap_of_square`, `GapFromSquare.lean`, continuous functional calculus
   of `R`): this squared inequality gives `ρ ‖u‖² ≤ ⟪B u, u⟫` for `u = R w` with `w ⟂ ker(1-R)`.
4. `ErgodicL2` identifies `ker(1 - R) = ker B` with the constants (`fixed_const`), and for
   `g ∈ 𝒜₀` the centered function `g - ∫g ∈ 𝒜` equals `R w` with `w ⟂ 1` by
   `FullMarkovTriple.resolvent_eq`.  So `ρ Var(g) ≤ ∫ Γ(g)`.

No semigroup, no differentiation in time, no stable class.  Needs `IsProbabilityMeasure μ`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E]

/-- The squared inequality for every vector. -/
theorem square_all (F : FullMarkovTriple E) [IsFiniteMeasure F.μ] {ρ : ℝ}
    (hρ : ∀ g ∈ F.A₀, ρ * ∫ x, F.Γ g g x ∂F.μ ≤ ∫ x, F.L g x * F.L g x ∂F.μ)
    (w : Lp ℝ 2 F.μ) :
    ρ * inner ℝ (w - (formData F.toMarkovTriple).R w) ((formData F.toMarkovTriple).R w) ≤
      ‖w - (formData F.toMarkovTriple).R w‖ ^ 2 := by
  let T := F.toMarkovTriple
  let S := formData T
  have hC : IsClosed {w : Lp ℝ 2 F.μ | ρ * inner ℝ (w - S.R w) (S.R w) ≤ ‖w - S.R w‖ ^ 2} := by
    apply isClosed_le <;> fun_prop
  have hsub : {y : Lp ℝ 2 F.μ | ∃ g ∈ T.A₀, (y : E → ℝ) =ᵐ[T.μ] g - T.L g} ⊆
      {w : Lp ℝ 2 F.μ | ρ * inner ℝ (w - S.R w) (S.R w) ≤ ‖w - S.R w‖ ^ 2} := by
    rintro y ⟨g, hg, hy⟩
    set g' : T.A₀ := ⟨g, hg⟩ with hg'
    have hyeq : y = toLp0 T g' - Lt0 T g' := by
      refine Lp.ext ?_
      filter_upwards [hy, Lp.coeFn_sub (toLp0 T g') (Lt0 T g'), coeFn_toLp0 T g',
        coeFn_Lt0 T g'] with x h1 h2 h3 h4
      rw [h1, h2]; simp only [Pi.sub_apply]; rw [h3, h4]
    have hRy : S.R y = toLp0 T g' := by
      have := S.R_resolvent ⟨toLp0 T g', ⟨g', rfl⟩⟩
      have e : S.opA ⟨toLp0 T g', ⟨g', rfl⟩⟩ = -Lt0 T g' := formA_apply T g'
      rw [e] at this
      rw [hyeq, sub_eq_add_neg]
      exact this
    have hdiff : y - S.R y = -Lt0 T g' := by rw [hRy, hyeq]; abel
    show ρ * inner ℝ (y - S.R y) (S.R y) ≤ ‖y - S.R y‖ ^ 2
    rw [hdiff, hRy, inner_neg_left, inner_Lt0_toLp0, norm_neg, ← real_inner_self_eq_norm_sq]
    have hLg2 : MemLp (T.L g) 2 T.μ := memLp2 T (T.L_mem g hg)
    have : inner ℝ (Lt0 T g') (Lt0 T g') = ∫ x, T.L g x * T.L g x ∂T.μ := by
      rw [Lt0_apply]; exact inner_toLp_toLp hLg2 hLg2
    rw [this, neg_neg]
    exact hρ g hg
  have hw : w ∈ closure {y : Lp ℝ 2 F.μ | ∃ g ∈ T.A₀, (y : E → ℝ) =ᵐ[T.μ] g - T.L g} := by
    rw [F.esa.closure_eq]; trivial
  exact closure_minimal hsub hC hw

/-- **Poincaré inequality for centered test functions, `ρ Var ≤ ℰ`.** -/
theorem rho_var_le_of (F : FullMarkovTriple E) [IsProbabilityMeasure F.μ] {ρ : ℝ}
    (hCD : ∀ g ∈ F.A₀, ρ * ∫ x, F.Γ g g x ∂F.μ ≤ ∫ x, F.L g x * F.L g x ∂F.μ)
    (herg : F.toMarkovTriple.ErgodicL2)
    {g : E → ℝ} (hg : g ∈ F.A₀) :
    ρ * ProbabilityTheory.variance g F.μ ≤ ∫ x, F.Γ g g x ∂F.μ := by
  let T := F.toMarkovTriple
  let S := formData T
  set m : ℝ := ∫ x, g x ∂F.μ with hm
  have hgA : g ∈ F.A := F.A₀_le g hg
  have hmA : (fun _ : E => m) ∈ F.A := by
    have := F.A.algebraMap_mem m
    exact this
  have hone : (1 : E → ℝ) ∈ F.A := F.A.one_mem
  have hgt : (fun x => g x - m) ∈ F.A := by
    have := F.A.sub_mem hgA hmA
    exact this
  have hLt : F.L (fun x => g x - m) = F.L g := by
    have e : (fun x => g x - m) = g + (-m) • (1 : E → ℝ) := by
      funext x; simp [sub_eq_add_neg]
    rw [e, F.L_add_A g hgA _ (F.A.smul_mem hone _), F.L_smul_A _ _ hone, F.L_one]
    simp
  have hg2 : MemLp g 2 F.μ := memLp2 T hg
  have hLg2 : MemLp (F.L g) 2 F.μ := memLp2 T (T.L_mem g hg)
  have hf : MemLp (fun x => g x - m) 2 F.μ := hg2.sub (memLp_const m)
  have hLf : MemLp (F.L (fun x => g x - m)) 2 F.μ := by rw [hLt]; exact hLg2
  have hres := F.resolvent_eq hgt hf hLf
  set u : Lp ℝ 2 F.μ := hf.toLp _ with hu
  set w : Lp ℝ 2 F.μ := hf.toLp _ - hLf.toLp (F.L fun x => g x - m) with hw
  have hRw : S.R w = u := hres
  have hint_g : Integrable g F.μ := integrable_of_mem T hg
  have hint_Lg : Integrable (F.L g) F.μ := integrable_of_mem T (T.L_mem g hg)
  have hLint : ∫ x, F.L g x ∂F.μ = 0 := F.integral_L hg
  -- orthogonality to the fixed space
  have horth : ∀ v : Lp ℝ 2 F.μ, S.R v = v → inner ℝ w v = 0 := by
    intro v hv
    obtain ⟨c, hc⟩ := fixed_const F herg v hv
    have hvc : v = (memLp_const c).toLp (fun _ => c) := Lp.ext (hc.trans (MemLp.coeFn_toLp _).symm)
    have e1 : inner ℝ (hf.toLp _) v = ∫ x, (g x - m) * c ∂F.μ := by
      rw [hvc]; exact inner_toLp_toLp hf (memLp_const c)
    have e2 : inner ℝ (hLf.toLp _) v = ∫ x, F.L g x * c ∂F.μ := by
      rw [hvc, inner_toLp_toLp hLf (memLp_const c)]
      simp only [hLt]
    rw [hw, inner_sub_left, e1, e2, integral_mul_const, integral_mul_const,
      integral_sub hint_g (integrable_const m), hLint]
    simp [hm]
  have hgap := gap_of_square (R := S.R) S.R_unitOp ρ (square_all F hCD) horth
  rw [hRw] at hgap
  have hwu : w - u = -hLf.toLp (F.L fun x => g x - m) := by rw [hw]; abel
  rw [hwu, inner_neg_left] at hgap
  have n1 : ‖u‖ ^ 2 = ∫ x, (g x - m) * (g x - m) ∂F.μ := by
    rw [← real_inner_self_eq_norm_sq]; exact inner_toLp_toLp hf hf
  have n2 : inner ℝ (hLf.toLp (F.L fun x => g x - m)) u =
      ∫ x, F.L g x * (g x - m) ∂F.μ := by
    rw [hu, inner_toLp_toLp hLf hf]; simp only [hLt]
  rw [n1, n2] at hgap
  have hvar : ProbabilityTheory.variance g F.μ = ∫ x, (g x - m) * (g x - m) ∂F.μ := by
    rw [ProbabilityTheory.variance_eq_integral hg2.aestronglyMeasurable.aemeasurable]
    simp only [← sq]
    rfl
  have hprod : Integrable (fun x => F.L g x * g x) F.μ :=
    integrable_of_mem T (T.A₀.mul_mem (T.L_mem g hg) hg)
  have hexp : ∫ x, F.L g x * (g x - m) ∂F.μ = ∫ x, g x * F.L g x ∂F.μ := by
    have : (fun x => F.L g x * (g x - m)) = fun x => F.L g x * g x - m * F.L g x := by
      funext x; ring
    rw [this, integral_sub hprod (hint_Lg.const_mul m), integral_const_mul, hLint]
    simp only [mul_zero, sub_zero]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [mul_comm])
  rw [hexp, T.ibp g hg g hg, neg_neg] at hgap
  rw [hvar]
  exact hgap

/-- `ρ Var ≤ ℰ` from `CD(ρ,n)` for every `n` (the dimensional term is dropped). -/
theorem rho_var_le (F : FullMarkovTriple E) [IsProbabilityMeasure F.μ] {ρ : ℝ} {n : ℝ≥0∞}
    (hCD : F.toMarkovTriple.CD ρ n) (herg : F.toMarkovTriple.ErgodicL2)
    {g : E → ℝ} (hg : g ∈ F.A₀) :
    ρ * ProbabilityTheory.variance g F.μ ≤ ∫ x, F.Γ g g x ∂F.μ :=
  rho_var_le_of F (fun _ hg' => F.rho_integral_le hCD hg') herg hg

/-- **Phase 4, first abstract Bakry–Émery theorem.**
For a full Markov triple on a probability space satisfying `CD(ρ,∞)` (`ρ > 0`, on `𝒜₀`) and
`ErgodicL2`, the Poincaré inequality `PI(1/ρ)` holds on `𝒜₀`: `Var_μ(f) ≤ (1/ρ) ∫ Γ(f,f) dμ`. -/
theorem poincare_of_CD_infty (F : FullMarkovTriple E) [IsProbabilityMeasure F.μ] {ρ : ℝ}
    (hρ : 0 < ρ) (hCD : F.toMarkovTriple.CD ρ ∞) (herg : F.toMarkovTriple.ErgodicL2) :
    F.toMarkovTriple.PoincareIneq (1 / ρ) := by
  refine ⟨inferInstance, fun f hf => ?_⟩
  have h := rho_var_le F hCD herg hf
  show ProbabilityTheory.variance f F.μ ≤ 1 / ρ * ∫ x, F.Γ f f x ∂F.μ
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hρ]
  linarith

/-- **Lichnerowicz** (finite dimension): `CD(ρ,n)`, `1 < n ≤ ∞`, `ρ > 0`, ergodic, probability ⟹
`PI((n-1)/(ρ n))`, i.e. the spectral gap is `ρ n/(n-1)` (`n = ∞`: `ρ`).  Stated with
`c = (n⁻¹).toReal < 1`: `PI((1 - c)/ρ)`. -/
theorem poincare_of_CD_dim (F : FullMarkovTriple E) [IsProbabilityMeasure F.μ] {ρ : ℝ}
    {n : ℝ≥0∞} (hρ : 0 < ρ) (hn : 1 < n) (hCD : F.toMarkovTriple.CD ρ n)
    (herg : F.toMarkovTriple.ErgodicL2) :
    F.toMarkovTriple.PoincareIneq ((1 - (n⁻¹).toReal) / ρ) := by
  have hc : (n⁻¹).toReal < 1 := by
    have h1 : n⁻¹ < 1 := ENNReal.inv_lt_one.2 hn
    have h2 : n⁻¹ ≠ ∞ := ne_top_of_lt h1
    have := (ENNReal.toReal_lt_toReal h2 ENNReal.one_ne_top).2 h1
    simpa using this
  set c : ℝ := (n⁻¹).toReal with hcdef
  have hc1 : 0 < 1 - c := by linarith
  have hint : ∀ g ∈ F.A₀, (ρ / (1 - c)) * ∫ x, F.Γ g g x ∂F.μ ≤ ∫ x, F.L g x * F.L g x ∂F.μ := by
    intro g hg
    have h := F.rho_integral_le_dim hCD hg
    rw [div_mul_eq_mul_div, div_le_iff₀ hc1]
    nlinarith [h]
  refine ⟨inferInstance, fun f hf => ?_⟩
  have h := rho_var_le_of F hint herg hf
  show ProbabilityTheory.variance f F.μ ≤ (1 - c) / ρ * ∫ x, F.Γ f f x ∂F.μ
  have hρ' : 0 < ρ / (1 - c) := by positivity
  have key : (1 - c) / ρ = (ρ / (1 - c))⁻¹ := by rw [inv_div]
  rw [key, inv_mul_eq_div, le_div_iff₀ hρ']
  linarith

end MarkovTriple.Hilbert
