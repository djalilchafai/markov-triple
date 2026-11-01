import Mathlib
import MarkovTriple.BGL.Calculus.Density

/-!
# The logarithmic Sobolev inequality extends from `𝒜₀` to `𝒟(ℰ)` (audit M2)

`DiffusionTriple.LS.extend`: if `T.LS C D` (i.e. `Ent(f²) ≤ 2Cℰ(f) + D∫f²` on `𝒜₀`), then for every
`u ∈ 𝒟(ℰ)` the function `u² log u²` is integrable and `Ent(u²) ≤ 2C ℰ(u) + D ∫u²`.

Proof: approximate `u` by `a_n ∈ 𝒜₀` (`formDomain_approx`: `L²` convergence, `ℰ(a_n) → ℰ(u)`); pass to an
a.e.-convergent subsequence; apply Fatou (`fatou_mul_log`) to `φ(a_n²) + 1 ≥ 0` with
`φ(y) = y log y ≥ y − 1`; the terms `m_n log m_n`, `m_n = ∫ a_n²`, converge by continuity of
`y ↦ y log y`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

lemma mul_log_add_one_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ y * Real.log y + 1 := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  · have := Real.one_sub_inv_le_log_of_pos hy
    have h2 : y * (1 - y⁻¹) ≤ y * Real.log y := mul_le_mul_of_nonneg_left this hy.le
    have h3 : y * (1 - y⁻¹) = y - 1 := by field_simp
    linarith

/-- Fatou for the entropy functional `∫ g² log g²` on a probability space. -/
lemma fatou_mul_log {μ : Measure E} [IsProbabilityMeasure μ] (f : ℕ → E → ℝ) (g : E → ℝ)
    (hfm : ∀ k, Measurable (f k)) (hgm : AEMeasurable g μ)
    (hint : ∀ k, Integrable (fun x => f k x ^ 2 * Real.log (f k x ^ 2)) μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x)))
    (b : ℕ → ℝ) (B : ℝ) (hb : Tendsto b atTop (𝓝 B))
    (hLS : ∀ k, (∫ x, f k x ^ 2 * Real.log (f k x ^ 2) ∂μ) + 1 ≤ b k) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ ∧
      (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂μ) + 1 ≤ B := by
  have hint1 : ∀ k, ∫ x, (f k x ^ 2 * Real.log (f k x ^ 2) + 1) ∂μ =
      (∫ x, f k x ^ 2 * Real.log (f k x ^ 2) ∂μ) + 1 := fun k => by
    rw [integral_add (hint k) (integrable_const 1), integral_const, probReal_univ, one_smul]
  have hpos : ∀ k, 0 ≤ (∫ x, f k x ^ 2 * Real.log (f k x ^ 2) ∂μ) + 1 := fun k => by
    rw [← hint1 k]
    exact integral_nonneg (fun x => mul_log_add_one_nonneg (sq_nonneg _))
  have hB0 : 0 ≤ B := ge_of_tendsto hb (Filter.Eventually.of_forall fun k => (hpos k).trans (hLS k))
  have hFm : ∀ k, Measurable (fun x => ENNReal.ofReal (f k x ^ 2 * Real.log (f k x ^ 2) + 1)) :=
    fun k => ((Real.continuous_mul_log.measurable.comp ((hfm k).pow_const 2)).add_const 1).ennreal_ofReal
  have hfat := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hFm
  have hlimF : ∀ᵐ x ∂μ, liminf (fun k => ENNReal.ofReal (f k x ^ 2 * Real.log (f k x ^ 2) + 1)) atTop
      = ENNReal.ofReal (g x ^ 2 * Real.log (g x ^ 2) + 1) := by
    filter_upwards [hconv] with x hx
    have : Tendsto (fun k => ENNReal.ofReal (f k x ^ 2 * Real.log (f k x ^ 2) + 1)) atTop
        (𝓝 (ENNReal.ofReal (g x ^ 2 * Real.log (g x ^ 2) + 1))) :=
      ENNReal.tendsto_ofReal
        (((Real.continuous_mul_log.tendsto _).comp (hx.pow 2)).add_const 1)
    exact this.liminf_eq
  have hlintF : ∀ k, ∫⁻ x, ENNReal.ofReal (f k x ^ 2 * Real.log (f k x ^ 2) + 1) ∂μ =
      ENNReal.ofReal ((∫ x, f k x ^ 2 * Real.log (f k x ^ 2) ∂μ) + 1) := by
    intro k
    rw [← hint1 k]
    exact (ofReal_integral_eq_lintegral_ofReal ((hint k).add (integrable_const 1))
      (Filter.Eventually.of_forall fun x => mul_log_add_one_nonneg (sq_nonneg _))).symm
  have hle1 : liminf (fun k => ∫⁻ x, ENNReal.ofReal (f k x ^ 2 * Real.log (f k x ^ 2) + 1) ∂μ) atTop
      ≤ ENNReal.ofReal B := by
    have h2 : Tendsto (fun k => ENNReal.ofReal (b k)) atTop (𝓝 (ENNReal.ofReal B)) :=
      ENNReal.tendsto_ofReal hb
    rw [← h2.liminf_eq]
    refine liminf_le_liminf (Filter.Eventually.of_forall fun k => ?_)
    rw [hlintF k]
    exact ENNReal.ofReal_le_ofReal (hLS k)
  have hfin : ∫⁻ x, ENNReal.ofReal (g x ^ 2 * Real.log (g x ^ 2) + 1) ∂μ ≤ ENNReal.ofReal B := by
    refine le_trans (le_of_eq (lintegral_congr_ae (hlimF.mono fun x hx => hx.symm))) ?_
    exact hfat.trans hle1
  have hgm' : AEStronglyMeasurable (fun x => g x ^ 2 * Real.log (g x ^ 2) + 1) μ :=
    ((Real.continuous_mul_log.measurable.comp_aemeasurable (hgm.pow_const 2)).add_const 1).aestronglyMeasurable
  have hg0 : 0 ≤ᵐ[μ] fun x => g x ^ 2 * Real.log (g x ^ 2) + 1 :=
    Filter.Eventually.of_forall fun x => mul_log_add_one_nonneg (sq_nonneg _)
  have hgint : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2) + 1) μ :=
    ⟨hgm', (hasFiniteIntegral_iff_ofReal hg0).2 (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)⟩
  have hint_u : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ := by
    have := hgint.sub (integrable_const (1 : ℝ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  refine ⟨hint_u, ?_⟩
  have hIB : ∫ x, (g x ^ 2 * Real.log (g x ^ 2) + 1) ∂μ ≤ B := by
    have := (ofReal_integral_eq_lintegral_ofReal hgint hg0).trans_le hfin
    exact (ENNReal.ofReal_le_ofReal_iff hB0).1 this
  rwa [integral_add hint_u (integrable_const 1), integral_const, probReal_univ, one_smul] at hIB

namespace DiffusionTriple

variable (T : DiffusionTriple E)

theorem LS.extend {C D : ℝ} (h : T.LS C D) (u : T.formDomain) :
    Integrable (fun x => ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 * Real.log (((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2))
        T.μ ∧
      Ent T.μ (fun x => ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2) ≤
        2 * C * T.closedForm u u + D * ∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ := by
  unfold DiffusionTriple.LS LogSobolevIneq at h
  obtain ⟨hprob, hC, hD, hineq⟩ := h
  have := hprob
  obtain ⟨a, h1, -, h3⟩ := T.formDomain_approx u
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  have hconv : ∀ᵐ x ∂T.μ, Tendsto (fun k => (a (ns k)).1 x) atTop
      (𝓝 (((u : Lp ℝ 2 T.μ) : E → ℝ) x)) := by
    filter_upwards [hae, ae_all_iff.2 (fun k => coeFn_cls T (a (ns k)))] with x hx hx2
    exact hx.congr (fun k => hx2 k)
  have hsq : ∀ v : Lp ℝ 2 T.μ, ∫ x, (v : E → ℝ) x ^ 2 ∂T.μ = ‖v‖ ^ 2 := by
    intro v
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
  have hsqa : ∀ n, ∫ x, (a n).1 x ^ 2 ∂T.μ = ‖T.cls (a n)‖ ^ 2 := by
    intro n
    rw [← hsq]
    exact integral_congr_ae (by filter_upwards [coeFn_cls T (a n)] with x hx; rw [hx])
  have hmk : Tendsto (fun k => ∫ x, (a (ns k)).1 x ^ 2 ∂T.μ) atTop
      (𝓝 (∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ)) := by
    rw [hsq]
    simp only [hsqa]
    exact ((h1.comp hns.tendsto_atTop).norm).pow 2
  have hbk : Tendsto (fun k => 2 * C * T.ℰ (a (ns k)) (a (ns k)) +
        D * ∫ x, (a (ns k)).1 x ^ 2 ∂T.μ +
        (∫ x, (a (ns k)).1 x ^ 2 ∂T.μ) * Real.log (∫ x, (a (ns k)).1 x ^ 2 ∂T.μ) + 1) atTop
      (𝓝 (2 * C * T.closedForm u u + D * (∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ) +
        (∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ) *
          Real.log (∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ) + 1)) := by
    have e1 : Tendsto (fun k => T.ℰ (a (ns k)) (a (ns k))) atTop (𝓝 (T.closedForm u u)) :=
      h3.comp hns.tendsto_atTop
    have e2 := (Real.continuous_mul_log.tendsto _).comp hmk
    exact (((e1.const_mul (2 * C)).add (hmk.const_mul D)).add e2).add_const 1
  have hint : ∀ n, Integrable (fun x => (a n).1 x ^ 2 * Real.log ((a n).1 x ^ 2)) T.μ := fun n =>
    T.integrable_sq_mul_log_sq (a n).2
  have hLS : ∀ k, (∫ x, (a (ns k)).1 x ^ 2 * Real.log ((a (ns k)).1 x ^ 2) ∂T.μ) + 1 ≤
      2 * C * T.ℰ (a (ns k)) (a (ns k)) + D * ∫ x, (a (ns k)).1 x ^ 2 ∂T.μ +
        (∫ x, (a (ns k)).1 x ^ 2 ∂T.μ) * Real.log (∫ x, (a (ns k)).1 x ^ 2 ∂T.μ) + 1 := by
    intro k
    have := hineq (a (ns k)).1 (a (ns k)).2
    unfold Ent at this
    have e : energy T.μ T.Γ (a (ns k)).1 = T.ℰ (a (ns k)) (a (ns k)) := rfl
    rw [e] at this
    linarith
  obtain ⟨hI, hB⟩ := fatou_mul_log (μ := T.μ) (fun k => (a (ns k)).1)
    ((u : Lp ℝ 2 T.μ) : E → ℝ) (fun k => T.measurable _ (a (ns k)).2)
    (Lp.aestronglyMeasurable (u : Lp ℝ 2 T.μ)).aemeasurable (fun k => hint (ns k)) hconv _ _ hbk hLS
  refine ⟨hI, ?_⟩
  unfold Ent
  linarith

end DiffusionTriple

end MarkovTriple.BGL
