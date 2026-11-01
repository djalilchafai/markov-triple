import Mathlib
import MarkovTriple.BGL.Theory.Poincare
import MarkovTriple.BGL.Theory.LogSobolev

/-!
# Entropy convergence `∫ Θ(ε + P_s φ) → Θ(ε + ∫ φ)` as `s → ∞` (from the spectral gap)

Under `CD(ρ, ·)`, `ρ > 0`, probability measure: `Poincaré ⇒ L²` exponential decay of `P_s` on the
mean-zero part (`DiffusionTriple.expDecay_of_PI`), hence `P_s φ → ∫ φ` in `L²`, and, `Θ(r) = r log r`
being Lipschitz on `[ε, ε + M]`, `∫ Θ(ε + P_s φ) → Θ(ε + ∫ φ)`.  This is the "limit at infinity"
ingredient of the entropy interpolation (it is NOT a hypothesis of `EntropyInterpolation`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

lemma lipschitz_mul_log {ε M a b : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (ha : a ∈ Icc ε (ε + M))
    (hb : b ∈ Icc ε (ε + M)) :
    |a * Real.log a - b * Real.log b| ≤
      (|Real.log ε| + |Real.log (ε + M)| + 1) * |a - b| := by
  have hconv : Convex ℝ (Icc ε (ε + M)) := convex_Icc _ _
  have key := hconv.norm_image_sub_le_of_norm_deriv_le (f := fun r : ℝ => r * Real.log r)
    (C := |Real.log ε| + |Real.log (ε + M)| + 1)
    (fun r hr => by
      have : r ≠ 0 := by linarith [hr.1]
      exact (differentiableAt_id.mul (Real.differentiableAt_log this)))
    (fun r hr => by
      have hr0 : r ≠ 0 := by linarith [hr.1]
      rw [Real.deriv_mul_log hr0, Real.norm_eq_abs]
      have h1 : Real.log ε ≤ Real.log r := Real.log_le_log hε hr.1
      have h2 : Real.log r ≤ Real.log (ε + M) := Real.log_le_log (by linarith [hr.1]) hr.2
      have := neg_abs_le (Real.log ε)
      have := le_abs_self (Real.log (ε + M))
      have := abs_nonneg (Real.log ε)
      have := abs_nonneg (Real.log (ε + M))
      rw [abs_le]
      constructor <;> linarith)
    hb ha
  simpa [Real.norm_eq_abs] using key

namespace FullTriple

variable (T : FullTriple E)

lemma CD_infty_of_CD {ρ : ℝ} {n : ℝ≥0∞} (h : T.CD ρ n) : T.CD ρ ∞ := by
  refine ⟨le_top, fun f hf => ?_⟩
  filter_upwards [h.2 f hf] with x hx
  have : 0 ≤ (n⁻¹).toReal * (T.L f x) ^ 2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  simp only [ENNReal.inv_top, ENNReal.toReal_zero, zero_mul, add_zero]
  linarith

variable [IsProbabilityMeasure T.μ]

/-- **`∫ Θ(ε + P_s φ) → Θ(ε + ∫ φ)`** as `s → ∞` (`CD(ρ,·)`, `ρ > 0`, probability measure). -/
theorem tendsto_entE {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ) (hCD : T.CD ρ n) (φ : T.A₀) {ε : ℝ}
    (hε : 0 < ε) (h0 : 0 ≤ᵐ[T.μ] φ.1) :
    Tendsto (T.entE φ ε) atTop
      (𝓝 ((ε + ∫ x, φ.1 x ∂T.μ) * Real.log (ε + ∫ x, φ.1 x ∂T.μ))) := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  obtain ⟨C0, hC0⟩ := T.bounded φ.1 φ.2
  set M : ℝ := max C0 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hφM : ∀ x, φ.1 x ≤ M := fun x => (le_abs_self _).trans ((hC0 x).trans (le_max_left _ _))
  set m' : ℝ := ∫ x, φ.1 x ∂T.μ with hm'
  have hm'0 : 0 ≤ m' := integral_nonneg_of_ae h0
  have hm'M : m' ≤ M := by
    have : ∫ x, φ.1 x ∂T.μ ≤ ∫ _x, M ∂T.μ :=
      integral_mono (DiffusionTriple.integrable_of_mem T.toDiffusionTriple φ.2) (integrable_const M) hφM
    simpa using this
  set m : ℝ := ε + m' with hm
  have hmI : m ∈ Icc ε (ε + M) := ⟨by linarith, by linarith⟩
  -- the spectral decay
  have hPI := poincare_of_CD_infty T hρ (CD_infty_of_CD T hCD)
  have hdec := DiffusionTriple.expDecay_of_PI T.toDiffusionTriple T.esaProp hPI
  set u : Lp ℝ 2 T.μ := T.toDiffusionTriple.cls φ - m' • T.toDiffusionTriple.one2 with hu
  have hOrth : S.OrthFixed u := by
    intro v hv
    obtain ⟨c, hc⟩ := DiffusionTriple.fixed_const T.toDiffusionTriple T.ergodic v hv
    have hvc : v = c • T.toDiffusionTriple.one2 := by
      refine Lp.ext ?_
      filter_upwards [hc, T.toDiffusionTriple.coeFn_one2, Lp.coeFn_smul c T.toDiffusionTriple.one2] with x h1 h2 h3
      rw [h1, h3, Pi.smul_apply, h2]; simp
    rw [hvc, inner_smul_right, hu, inner_sub_left, inner_smul_left,
      DiffusionTriple.inner_cls_one2, DiffusionTriple.inner_one2_one2]
    simp [hm']
  set d : ℝ → Lp ℝ 2 T.μ := fun s => T.toDiffusionTriple.semigroup s.toNNReal (T.toDiffusionTriple.cls φ) - m' • T.toDiffusionTriple.one2 with hd
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖d s‖ ≤ Real.exp (-(1 / (1 / ρ)) * s) * ‖u‖ := by
    intro s hs
    have h := hdec u hOrth s.toNNReal
    have e : S.semigroup s.toNNReal u = d s := by
      have hsg : S.semigroup s.toNNReal T.toDiffusionTriple.one2 = T.toDiffusionTriple.one2 :=
        DiffusionTriple.semigroup_one2 T.toDiffusionTriple T.esaProp _
      rw [hu, map_sub, map_smul, hsg]
      rfl
    rw [e, Real.coe_toNNReal s hs] at h
    exact h
  have hlim0 : Tendsto (fun s : ℝ => Real.exp (-(1 / (1 / ρ)) * s) * ‖u‖) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => Real.exp (-(1 / (1 / ρ)) * s)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      refine tendsto_id.const_mul_atTop_of_neg ?_
      have : 0 < 1 / (1 / ρ) := by positivity
      linarith
    simpa using this.mul_const ‖u‖
  set K : ℝ := |Real.log ε| + |Real.log (ε + M)| + 1 with hK
  have hbound : ∀ s : ℝ, 0 ≤ s →
      ‖T.entE φ ε s - m * Real.log m‖ ≤ K * ‖d s‖ := by
    intro s hs
    have hy := T.entG_range φ hε hM h0 hφM s
    have hdae : ∀ᵐ x ∂T.μ, (d s : E → ℝ) x = T.Pt s.toNNReal φ x - m' := by
      filter_upwards [Lp.coeFn_sub (T.toDiffusionTriple.semigroup s.toNNReal (T.toDiffusionTriple.cls φ)) (m' • T.toDiffusionTriple.one2),
        Lp.coeFn_smul m' T.toDiffusionTriple.one2, T.toDiffusionTriple.coeFn_one2, T.Pt_ae s.toNNReal φ] with x h1 h2 h3 h4
      rw [hd]
      simp only
      rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4]; simp
    -- integrability of `g log g`
    have hgm : AEStronglyMeasurable (fun x => T.entG φ ε s x * Real.log (T.entG φ ε s x)) T.μ := by
      have h1 : Measurable (T.entG φ ε s) :=
        measurable_const.add (T.A_measurable _ (T.Pt_mem_A _ φ))
      exact (Real.continuous_mul_log.measurable.comp h1).aestronglyMeasurable
    have hbd : ∀ᵐ x ∂T.μ, ‖T.entG φ ε s x * Real.log (T.entG φ ε s x)‖ ≤
        (ε + M) * (|Real.log ε| + |Real.log (ε + M)|) := by
      filter_upwards [hy] with x hx
      have hpos : 0 < T.entG φ ε s x := lt_of_lt_of_le hε hx.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
      have h1 : Real.log ε ≤ Real.log (T.entG φ ε s x) := Real.log_le_log hε hx.1
      have h2 : Real.log (T.entG φ ε s x) ≤ Real.log (ε + M) :=
        Real.log_le_log hpos hx.2
      have hl : |Real.log (T.entG φ ε s x)| ≤ |Real.log ε| + |Real.log (ε + M)| := by
        have := neg_abs_le (Real.log ε)
        have := le_abs_self (Real.log (ε + M))
        have := abs_nonneg (Real.log ε)
        have := abs_nonneg (Real.log (ε + M))
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul hx.2 hl (abs_nonneg _) (by linarith)
    have hgi : Integrable (fun x => T.entG φ ε s x * Real.log (T.entG φ ε s x)) T.μ :=
      Integrable.of_bound hgm _ hbd
    have e1 : T.entE φ ε s - m * Real.log m =
        ∫ x, (T.entG φ ε s x * Real.log (T.entG φ ε s x) - m * Real.log m) ∂T.μ := by
      rw [integral_sub hgi (integrable_const _)]
      simp [entE]
    have hdi : Integrable (fun x => K * |(d s : E → ℝ) x|) T.μ :=
      ((Lp.memLp (d s)).integrable one_le_two).abs.const_mul K
    rw [e1]
    refine (norm_integral_le_of_norm_le hdi ?_).trans ?_
    · filter_upwards [hy, hdae] with x hx hxd
      rw [Real.norm_eq_abs, hxd]
      have := lipschitz_mul_log hε hM.le hx hmI
      have e : T.entG φ ε s x - m = T.Pt s.toNNReal φ x - m' := by simp [entG, hm]
      rw [e] at this
      exact this
    · rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      -- `∫ |d| ≤ ‖d‖`
      have h1 : ∫ x, |(d s : E → ℝ) x| ∂T.μ = inner ℝ |d s| T.toDiffusionTriple.one2 := by
        rw [L2_inner_eq]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_abs (d s), T.toDiffusionTriple.coeFn_one2] with x h1 h2
        rw [h1, h2, mul_one]
      rw [h1]
      calc inner ℝ |d s| T.toDiffusionTriple.one2 ≤ ‖|d s|‖ * ‖T.toDiffusionTriple.one2‖ := real_inner_le_norm _ _
        _ = ‖d s‖ := by
          have : ‖T.toDiffusionTriple.one2‖ = 1 := by
            have h := DiffusionTriple.inner_one2_one2 T.toDiffusionTriple
            rw [real_inner_self_eq_norm_sq] at h
            nlinarith [norm_nonneg T.toDiffusionTriple.one2]
          rw [this, mul_one, norm_abs_eq']
  have hsq : Tendsto (fun s : ℝ => T.entE φ ε s - m * Real.log m) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun s : ℝ => K * (Real.exp (-(1 / (1 / ρ)) * s) * ‖u‖)) ?_
      (by simpa using hlim0.const_mul K)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact (hbound s hs).trans (mul_le_mul_of_nonneg_left (hnorm s hs) (by positivity))
  have := hsq.add_const (m * Real.log m)
  simpa using this

end FullTriple

end MarkovTriple.BGL
