import Mathlib
import MarkovTriple.BGL.Instances.IntervalGen.Diffusion
import MarkovTriple.BGL.Theory.ESAOne

/-!
# `L` is NOT essentially self-adjoint on `C_c^∞(Ω)` for bounded open `Ω ⊆ ℝ` (G4)

`u = exp|_Ω ∈ L²(Ω)` satisfies `∫ u (f'' - f) = 0` for every `f ∈ 𝒜₀` (two integrations by parts against `exp` on `ℝ`;
no boundary terms since `f` has compact support): the range of `L - 1` on `𝒜₀` is not dense.  The Friedrichs generator is
self-adjoint and `1 - L` is onto, so `𝒜₀` cannot be a core: `DiffusionTriple.ESAProp` (F10) fails, hence no `FullTriple`
has `Ω.diff` as underlying diffusion triple.  See `STATEMENTS_R22_E1.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.Instances.IntervalGen

namespace BddOpen

variable (Ω : BddOpen)

lemma exp_ibp {f : ℝ → ℝ} (hf : f ∈ Ω.A₀) :
    ∫ x, Real.exp x * Lebesgue.Lf f x = ∫ x, Real.exp x * f x := by
  have hexp : Lebesgue.Sm Real.exp := Real.contDiff_exp
  have hd : deriv Real.exp = Real.exp := Real.deriv_exp
  have h1 := Lebesgue.ibp_cs hexp (A₀_smooth hf).deriv' (Or.inr (A₀_cs hf).deriv)
  have h2 := Lebesgue.ibp_cs hexp (A₀_smooth hf) (Or.inr (A₀_cs hf))
  rw [hd] at h1 h2
  unfold Lebesgue.Lf
  rw [h1, h2, neg_neg]

lemma memLp_exp : MemLp (fun x : ℝ => Real.exp x) 2 Ω.μ := by
  obtain ⟨r, hr⟩ := Ω.isBounded.subset_closedBall (0 : ℝ)
  refine MemLp.of_bound (C := Real.exp r) Real.continuous_exp.aestronglyMeasurable ?_
  refine (Ω.ae_μ_iff).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos x).le]
  have := hr hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact Real.exp_le_exp.2 ((le_abs_self x).trans this)

/-- the deficiency vector: `exp|_Ω` is a nonzero element of `L²(Ω)` orthogonal to `(L - 1)𝒜₀`. -/
theorem exp_orth : ∃ u : Lp ℝ 2 Ω.μ, u ≠ 0 ∧
    ∀ a : Ω.diff.A₀, inner ℝ u (Ω.diff.Lcls a - Ω.diff.cls a) = 0 := by
  refine ⟨Ω.memLp_exp.toLp _, ?_, ?_⟩
  · intro h0
    have hne : Ω.μ ≠ 0 := (Ω.isProb_μ).ne_zero
    have : (ae Ω.μ).NeBot := ae_neBot.2 hne
    have hae : (fun x : ℝ => Real.exp x) =ᵐ[Ω.μ] 0 := by
      have := (Lp.eq_zero_iff_ae_eq_zero (f := Ω.memLp_exp.toLp _)).1 h0
      filter_upwards [this, Ω.memLp_exp.coeFn_toLp] with x h1 h2
      rw [← h2]; exact h1
    obtain ⟨x, hx⟩ := hae.exists
    exact (Real.exp_pos x).ne' hx
  · intro a
    have ha : a.1 ∈ Ω.A₀ := a.2
    rw [L2_inner_eq]
    have e : ∫ x, (Ω.memLp_exp.toLp _ : ℝ → ℝ) x * (Ω.diff.Lcls a - Ω.diff.cls a : Lp ℝ 2 Ω.μ) x ∂Ω.μ
        = ∫ x, Real.exp x * (Lebesgue.Lf a.1 x - a.1 x) ∂Ω.μ := by
      refine integral_congr_ae ?_
      filter_upwards [Ω.memLp_exp.coeFn_toLp, Lp.coeFn_sub (Ω.diff.Lcls a) (Ω.diff.cls a),
        DiffusionTriple.coeFn_Lcls Ω.diff a, DiffusionTriple.coeFn_cls Ω.diff a] with x h1 h2 h3 h4
      rw [h1, h2]
      simp only [Pi.sub_apply, h3, h4]
    rw [e, Ω.integral_μ (fun x hx => by
      simp [zero_off (deriv_mem_A₀ (deriv_mem_A₀ ha)) hx, zero_off ha hx, Lebesgue.Lf])]
    have hi : ∀ g : ℝ → ℝ, HasCompactSupport g → Continuous g → Integrable (fun x => Real.exp x * g x) :=
      fun g hg hc => (Real.continuous_exp.mul hc).integrable_of_hasCompactSupport hg.mul_left
    simp_rw [mul_sub]
    have i1 : Integrable (fun x => Real.exp x * Lebesgue.Lf a.1 x) :=
      hi _ (A₀_cs (deriv_mem_A₀ (deriv_mem_A₀ ha)))
        (A₀_smooth (deriv_mem_A₀ (deriv_mem_A₀ ha))).continuous
    have i2 : Integrable (fun x => Real.exp x * a.1 x) :=
      hi _ (A₀_cs ha) (A₀_smooth ha).continuous
    rw [integral_sub i1 i2, Ω.exp_ibp ha, sub_self, mul_zero]

/-- **G4**: `𝒜₀ = C_c^∞(Ω)` is not a core for the Friedrichs generator: ESA (F10) fails. -/
theorem not_esaProp : ¬ Ω.diff.ESAProp := by
  intro hesa
  obtain ⟨u, hu0, horth⟩ := Ω.exp_orth
  set S := DiffusionTriple.formData Ω.diff with hS
  obtain ⟨h, hG⟩ := S.generator_R u
  have hG' : (Ω.diff.generator ⟨S.R u, h⟩ : Lp ℝ 2 Ω.μ) = S.R u - u := hG
  obtain ⟨a, ha1, ha2⟩ := hesa (S.R u) h
  have hlim : Tendsto (fun n => inner ℝ u (Ω.diff.Lcls (a n) - Ω.diff.cls (a n))) atTop
      (𝓝 (inner ℝ u (Ω.diff.generator ⟨S.R u, h⟩ - S.R u))) :=
    tendsto_const_nhds.inner (ha2.sub ha1)
  simp only [horth] at hlim
  have h0 := tendsto_nhds_unique hlim tendsto_const_nhds
  rw [hG', sub_sub_cancel_left, inner_neg_right, neg_eq_zero, real_inner_self_eq_norm_sq] at h0
  exact hu0 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h0.symm.symm))

/-- **G4**: no `FullTriple` structure has `Ω.diff` as underlying diffusion triple. -/
theorem no_fullTriple (T : FullTriple ℝ) : T.toDiffusionTriple ≠ Ω.diff := by
  intro h
  exact Ω.not_esaProp (h ▸ T.esaProp)

end BddOpen

end MarkovTriple.BGL.Instances.IntervalGen
