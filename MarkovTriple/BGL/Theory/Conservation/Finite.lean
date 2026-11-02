import Mathlib
import MarkovTriple.BGL.Theory.Conservation.Mass

/-!
# `ρ > 0` implies `μ(E) < ∞` (BGL Thm 3.3.23, second claim; proof of Thm 3.2.7)

If `μ` is infinite and the triple is ergodic (S10), `P_t u → 0` in `L²` for every `u`
(`Hilbert.FormData.exists_fixed_limit`, a `P`-fixed vector is a `L`-harmonic `L²` function, hence a constant,
hence `0` for infinite `μ`).  With the key estimate made uniform in `t` by the decay `e^{-ρ s}`
(`ρ > 0`): `|⟪P_t ζ_k − ζ_k, η²⟫| ≤ K(η) /(ρ (k+1))` for all `t`; letting `t → ∞` gives
`∫ ζ_k η² ≤ K(η)/(ρ(k+1))`, then `k → ∞` gives `∫ η² = 0` for `η = ζ_j`, contradicting `ζ_j → 1`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace ExtendedAlgebra

variable {D : DiffusionTriple E} {A : Subalgebra ℝ (E → ℝ)} (h : ExtendedAlgebra D A)
include h

/-- Uniform-in-`t` form of the key estimate when `ρ > 0`. -/
theorem abs_inner_Pt_sub_le_pos {ρ : ℝ} (hρ : 0 < ρ) (hGB : HasGradientBound D A ρ)
    (ζ c : D.A₀) (hc : c.1 =ᵐ[D.μ] D.Γ ζ.1 ζ.1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s : ℝ≥0, (D.semigroup s (D.cls c) : E → ℝ) ≤ᵐ[D.μ] fun _ => B)
    (η : D.A₀) (t : ℝ≥0) :
    |inner ℝ (D.semigroup t (D.cls ζ) - D.cls ζ) (D.cls ⟨η.1 * η.1, D.A₀.mul_mem η.2 η.2⟩)| ≤
      Real.sqrt B * D.Kconst η / ρ := by
  rw [D.inner_duhamel]
  set C := Real.sqrt B * D.Kconst η with hC
  have hC0 : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (D.Kconst_nonneg h η)
  have hcont : Continuous fun s : ℝ => C * Real.exp (-ρ * s) := by fun_prop
  have hle := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := (t : ℝ))
    (μ := volume) (NNReal.coe_nonneg t)
    (f := fun s : ℝ => inner ℝ (D.semigroup s.toNNReal (D.Lcls ζ))
      (D.cls ⟨η.1 * η.1, D.A₀.mul_mem η.2 η.2⟩))
    (g := fun s : ℝ => C * Real.exp (-ρ * s))
    (Filter.Eventually.of_forall fun s hs => by
      obtain ⟨hs0, hst⟩ := hs
      have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0.le
      have hb := h.abs_inner_le hGB ζ c hc hB0 hB η s.toNNReal
      rw [Real.norm_eq_abs]
      refine hb.trans ?_
      rw [hs', Real.sqrt_mul (Real.exp_pos _).le]
      have : Real.sqrt (Real.exp (-2 * ρ * s)) = Real.exp (-ρ * s) := by
        rw [show -2 * ρ * s = (-ρ * s) + (-ρ * s) by ring, Real.exp_add,
          Real.sqrt_mul_self (Real.exp_pos _).le]
      rw [this]
      nlinarith [Real.exp_pos (-ρ * s), D.Kconst_nonneg h η, Real.sqrt_nonneg B])
    (hcont.intervalIntegrable _ _)
  have hint : ∫ s in (0 : ℝ)..t, C * Real.exp (-ρ * s) = C * ((1 - Real.exp (-ρ * t)) / ρ) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := (t : ℝ))
      (f := fun s : ℝ => -(1 / ρ) * Real.exp (-ρ * s)) (f' := fun s => Real.exp (-ρ * s))
      (fun s _ => by
        have h1 : HasDerivAt (fun s : ℝ => Real.exp (-ρ * s)) (Real.exp (-ρ * s) * (-ρ)) s := by
          have := ((hasDerivAt_id s).const_mul (-ρ)).exp
          simpa using this
        have := h1.const_mul (-(1 / ρ))
        convert this using 1
        field_simp)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    rw [this]; simp only [mul_zero, Real.exp_zero]; field_simp; ring
  rw [hint] at hle
  have hexp : 0 < Real.exp (-ρ * t) := Real.exp_pos _
  have h2 : C * ((1 - Real.exp (-ρ * t)) / ρ) ≤ C / ρ := by
    have h3 : (1 - Real.exp (-ρ * t)) / ρ ≤ 1 / ρ :=
      div_le_div_of_nonneg_right (by linarith) hρ.le
    calc C * ((1 - Real.exp (-ρ * t)) / ρ) ≤ C * (1 / ρ) := mul_le_mul_of_nonneg_left h3 hC0
      _ = C / ρ := by ring
  rw [Real.norm_eq_abs] at hle
  exact hle.trans h2

end ExtendedAlgebra

namespace DiffusionTriple

/-- Ergodicity (S10) and infinite `μ`: `P_t u → 0` in `L²` for every `u` (BGL Sect. 1.6 / proof of
Thm 3.2.7). -/
theorem semigroup_tendsto_zero (D : DiffusionTriple E)
    (herg : ∀ (u : Lp ℝ 2 D.μ) (hu : u ∈ D.generator.domain), D.generator ⟨u, hu⟩ = 0 →
      ∃ c : ℝ, (u : E → ℝ) =ᵐ[D.μ] fun _ => c)
    (hinf : D.μ univ = ∞) (u : Lp ℝ 2 D.μ) :
    Tendsto (fun t : ℝ≥0 => D.semigroup t u) atTop (𝓝 0) := by
  obtain ⟨w, hw, hfix⟩ := (formData D).exists_fixed_limit u
  obtain ⟨hdom, hG⟩ := (formData D).fixed_mem_kernel hfix
  obtain ⟨c, hc⟩ := herg w hdom hG
  have hc0 : c = 0 := by
    have hm : MemLp (fun _ : E => c) 2 D.μ := (Lp.memLp w).ae_eq hc
    rcases (memLp_const_iff (by norm_num) (by simp)).1 hm with h0 | hlt
    · exact h0
    · exact absurd hinf (ne_of_lt hlt)
  have hw0 : w = 0 := by
    refine Lp.ext ?_
    filter_upwards [hc, Lp.coeFn_zero ℝ 2 D.μ] with x h1 h2
    rw [h1, h2, hc0]; rfl
  rw [hw0] at hw
  exact hw

end DiffusionTriple

namespace ExtendedAlgebra

variable {D : DiffusionTriple E} {A : Subalgebra ℝ (E → ℝ)} (h : ExtendedAlgebra D A)
include h

/-- **`ρ > 0` implies `μ(E) < ∞` (BGL Thm 3.3.23, second claim).**  A complete, ergodic (S10) triple
with the weak gradient bound for some `ρ > 0` has finite measure (then a probability measure,
`finite_prob`). -/
theorem isFiniteMeasure_of_complete {ρ : ℝ} (hρ : 0 < ρ) (hGB : HasGradientBound D A ρ)
    (hC : D.IsComplete)
    (herg : ∀ (u : Lp ℝ 2 D.μ) (hu : u ∈ D.generator.domain), D.generator ⟨u, hu⟩ = 0 →
      ∃ c : ℝ, (u : E → ℝ) =ᵐ[D.μ] fun _ => c) :
    IsFiniteMeasure D.μ := by
  by_contra hnf
  have hinf : D.μ univ = ∞ := by
    by_contra hne; exact hnf ⟨lt_top_iff_ne_top.2 hne⟩
  obtain ⟨ζ, hex, hζ0, hζΓ⟩ := hC.isExhaustion
  have hζle : ∀ᵐ x ∂D.μ, ∀ k, ζ k x ≤ 1 := hex.le_one_ae
  have hζ0' : ∀ᵐ x ∂D.μ, ∀ k, 0 ≤ ζ k x := ae_all_iff.2 hζ0
  have hζlim := hex.2.2
  have hζm : ∀ k, AEStronglyMeasurable (ζ k) D.μ := fun k =>
    (D.measurable _ (hex.1 k)).aestronglyMeasurable
  have hj : ∀ j, ∫ x, ζ j x * ζ j x ∂D.μ ≤ 0 := by
    intro j
    set η : D.A₀ := ⟨ζ j, hex.1 j⟩ with hη
    set ξ : D.A₀ := ⟨η.1 * η.1, D.A₀.mul_mem η.2 η.2⟩ with hξ
    have hξx : ∀ x, ξ.1 x = ζ j x * ζ j x := fun x => rfl
    have hξint : Integrable ξ.1 D.μ := D.integrable_of_mem ξ.2
    have hξm : AEStronglyMeasurable ξ.1 D.μ := (D.measurable _ ξ.2).aestronglyMeasurable
    have hξ0 : ∀ x, 0 ≤ ξ.1 x := fun x => by rw [hξx]; exact mul_self_nonneg _
    set K := D.Kconst η with hK
    have hk : ∀ k : ℕ, ∫ x, ζ k x * ξ.1 x ∂D.μ ≤ K / (ρ * ((k : ℝ) + 1)) := by
      intro k
      set c : D.A₀ := ⟨D.Γ (ζ k) (ζ k), D.Γ_mem _ (hex.1 k) _ (hex.1 k)⟩ with hc
      have hBk : ∀ s : ℝ≥0, (D.semigroup s (D.cls c) : E → ℝ) ≤ᵐ[D.μ]
          fun _ => (1 / ((k : ℝ) + 1)) ^ 2 := by
        intro s
        refine D.semigroup_le_const s _ (by positivity) ?_
        filter_upwards [D.coeFn_cls c, hζΓ k] with x h1 h2
        rw [h1]; exact h2
      have hb : ∀ t : ℝ≥0, |inner ℝ (D.semigroup t (D.cls ⟨ζ k, hex.1 k⟩) -
          D.cls ⟨ζ k, hex.1 k⟩) (D.cls ξ)| ≤ Real.sqrt ((1 / ((k : ℝ) + 1)) ^ 2) * K / ρ :=
        fun t => h.abs_inner_Pt_sub_le_pos hρ hGB ⟨ζ k, hex.1 k⟩ c (Filter.EventuallyEq.refl _ _)
          (by positivity) hBk η t
      have hlim : Tendsto (fun t : ℝ≥0 => |inner ℝ (D.semigroup t (D.cls ⟨ζ k, hex.1 k⟩) -
          D.cls ⟨ζ k, hex.1 k⟩) (D.cls ξ)|) atTop
          (𝓝 |inner ℝ ((0 : Lp ℝ 2 D.μ) - D.cls ⟨ζ k, hex.1 k⟩) (D.cls ξ)|) :=
        (((D.semigroup_tendsto_zero herg hinf (D.cls ⟨ζ k, hex.1 k⟩)).sub_const _).inner
          tendsto_const_nhds).abs
      have hle := le_of_tendsto' hlim hb
      have e : inner ℝ ((0 : Lp ℝ 2 D.μ) - D.cls ⟨ζ k, hex.1 k⟩) (D.cls ξ) =
          -∫ x, ζ k x * ξ.1 x ∂D.μ := by
        rw [zero_sub, inner_neg_left, L2_inner_eq]
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [D.coeFn_cls ⟨ζ k, hex.1 k⟩, D.coeFn_cls ξ] with x h1 h2
        rw [h1, h2]
      have hnn : 0 ≤ ∫ x, ζ k x * ξ.1 x ∂D.μ := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [hζ0 k] with x hx
        exact mul_nonneg hx (hξ0 x)
      rw [e, abs_neg, abs_of_nonneg hnn, Real.sqrt_sq (by positivity)] at hle
      calc ∫ x, ζ k x * ξ.1 x ∂D.μ ≤ 1 / ((k : ℝ) + 1) * K / ρ := hle
        _ = K / (ρ * ((k : ℝ) + 1)) := by field_simp
    have hT : Tendsto (fun k : ℕ => ∫ x, ζ k x * ξ.1 x ∂D.μ) atTop (𝓝 (∫ x, ξ.1 x ∂D.μ)) := by
      refine tendsto_integral_of_dominated_convergence (μ := D.μ) ξ.1
        (fun k => (hζm k).mul hξm) hξint (fun k => ?_) ?_
      · filter_upwards [hζ0' , hζle] with x h1 h2
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hξ0 x),
          abs_of_nonneg (h1 k)]
        exact mul_le_of_le_one_left (hξ0 x) (h2 k)
      · filter_upwards [hζlim] with x hx
        simpa using hx.mul_const (ξ.1 x)
    have hT2 : Tendsto (fun k : ℕ => K / (ρ * ((k : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (K / ρ)
      simp only [mul_zero] at this
      refine this.congr (fun k => ?_)
      field_simp
    have := le_of_tendsto_of_tendsto' hT hT2 hk
    simpa [hξx] using this
  have hz : ∀ j, ∀ᵐ x ∂D.μ, ζ j x * ζ j x = 0 := by
    intro j
    have hint : Integrable (fun x => ζ j x * ζ j x) D.μ := by
      exact D.integrable_of_mem (D.A₀.mul_mem (hex.1 j) (hex.1 j))
    have hnn : 0 ≤ᵐ[D.μ] fun x => ζ j x * ζ j x :=
      Filter.Eventually.of_forall fun x => mul_self_nonneg _
    have h0 : ∫ x, ζ j x * ζ j x ∂D.μ = 0 :=
      le_antisymm (hj j) (integral_nonneg_of_ae hnn)
    exact (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0
  have hfalse : ∀ᵐ x ∂D.μ, False := by
    filter_upwards [ae_all_iff.2 hz, hζlim] with x hx hl
    have h0 : ∀ j, ζ j x = 0 := fun j => mul_self_eq_zero.1 (hx j)
    have : Tendsto (fun k => ζ k x) atTop (𝓝 0) := by
      simp [h0]
    exact one_ne_zero (tendsto_nhds_unique hl this)
  have h0 : D.μ univ = 0 := by
    have := ae_iff.1 hfalse
    simpa using this
  rw [h0] at hinf
  exact ENNReal.zero_ne_top hinf

end ExtendedAlgebra

/-- Full-triple form of `ρ > 0 ⇒ μ(E) < ∞` (Thm 3.3.23), with the interpolation hypothesis for the
gradient bound; S10 is the field `ergodic`. -/
theorem FullTriple.isFiniteMeasure_of_complete {ρ : ℝ} {n : ℝ≥0∞} (T : FullTriple E)
    (hρ : 0 < ρ) (hCD : T.CD ρ n) (hG : T.GradientInterpolation)
    (hC : T.toDiffusionTriple.IsComplete) : IsFiniteMeasure T.μ :=
  T.extendedAlgebra.isFiniteMeasure_of_complete hρ (T.hasGradientBound hCD hG) hC T.ergodic

end MarkovTriple.BGL
