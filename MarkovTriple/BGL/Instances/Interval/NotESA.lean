import Mathlib
import MarkovTriple.BGL.Instances.Interval.Diffusion
import MarkovTriple.BGL.Theory.ESAOne

/-!
# `L` is NOT essentially self-adjoint on `C_c^∞((0,1))` (I4)

`u = exp|_(0,1) ∈ L²((0,1))` satisfies `∫ u (f'' - f) = 0` for every `f ∈ 𝒜₀` (two integrations by parts
against `exp`, no boundary terms since `f` has compact support in `(0,1)`): the range of `L - 1` on `𝒜₀` is
not dense.  The Friedrichs generator is self-adjoint and `1 - L` is onto, so `𝒜₀` cannot be a core:
`DiffusionTriple.ESAProp` (F10) fails, hence no `FullTriple` has `ivDiff` as underlying diffusion triple.
See `STATEMENTS_R21_Interval.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.Instances.Interval

lemma iv_exp_ibp {f : ℝ → ℝ} (hf : f ∈ ivA₀) :
    ∫ x, Real.exp x * Lebesgue.Lf f x = ∫ x, Real.exp x * f x := by
  have hexp : Lebesgue.Sm Real.exp := Real.contDiff_exp
  have hd : deriv Real.exp = Real.exp := Real.deriv_exp
  have h1 := Lebesgue.ibp_cs hexp (ivA₀_smooth hf).deriv' (Or.inr (ivA₀_cs hf).deriv)
  have h2 := Lebesgue.ibp_cs hexp (ivA₀_smooth hf) (Or.inr (ivA₀_cs hf))
  rw [hd] at h1 h2
  unfold Lebesgue.Lf
  rw [h1, h2, neg_neg]

lemma memLp_exp_iv : MemLp (fun x : ℝ => Real.exp x) 2 ivμ := by
  refine MemLp.of_bound (C := Real.exp 1) Real.continuous_exp.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos x).le]
  exact Real.exp_le_exp.2 hx.2.le

/-- the deficiency vector: `exp|_(0,1)` is a nonzero element of `L²((0,1))` orthogonal to `(L - 1)𝒜₀`. -/
theorem iv_exp_orth : ∃ u : Lp ℝ 2 ivμ, u ≠ 0 ∧
    ∀ a : ivDiff.A₀, inner ℝ u (ivDiff.Lcls a - ivDiff.cls a) = 0 := by
  refine ⟨memLp_exp_iv.toLp _, ?_, ?_⟩
  · intro h0
    have hne : ivμ ≠ 0 := IsProbabilityMeasure.ne_zero _
    have : (ae ivμ).NeBot := ae_neBot.2 hne
    have hae : (fun x : ℝ => Real.exp x) =ᵐ[ivμ] 0 := by
      have := (Lp.eq_zero_iff_ae_eq_zero (f := memLp_exp_iv.toLp _)).1 h0
      filter_upwards [this, memLp_exp_iv.coeFn_toLp] with x h1 h2
      rw [← h2]; exact h1
    obtain ⟨x, hx⟩ := hae.exists
    exact (Real.exp_pos x).ne' hx
  · intro a
    have ha : a.1 ∈ ivA₀ := a.2
    rw [L2_inner_eq]
    have hL : ivDiff.L a.1 = Lebesgue.Lf a.1 := rfl
    have e : ∫ x, (memLp_exp_iv.toLp _ : ℝ → ℝ) x * (ivDiff.Lcls a - ivDiff.cls a : Lp ℝ 2 ivμ) x ∂ivμ
        = ∫ x, Real.exp x * (Lebesgue.Lf a.1 x - a.1 x) ∂ivμ := by
      refine integral_congr_ae ?_
      filter_upwards [memLp_exp_iv.coeFn_toLp, Lp.coeFn_sub (ivDiff.Lcls a) (ivDiff.cls a),
        DiffusionTriple.coeFn_Lcls ivDiff a, DiffusionTriple.coeFn_cls ivDiff a] with x h1 h2 h3 h4
      rw [h1, h2]
      simp only [Pi.sub_apply, h3, h4]
    rw [e, integral_iv (fun x hx => by
      simp [zero_off (deriv_mem_ivA₀ (deriv_mem_ivA₀ ha)) hx, zero_off ha hx, Lebesgue.Lf])]
    have hi : ∀ g : ℝ → ℝ, HasCompactSupport g → Continuous g → Integrable (fun x => Real.exp x * g x) :=
      fun g hg hc => (Real.continuous_exp.mul hc).integrable_of_hasCompactSupport hg.mul_left
    simp_rw [mul_sub]
    have i1 : Integrable (fun x => Real.exp x * Lebesgue.Lf a.1 x) :=
      hi _ (ivA₀_cs (deriv_mem_ivA₀ (deriv_mem_ivA₀ ha)))
        (ivA₀_smooth (deriv_mem_ivA₀ (deriv_mem_ivA₀ ha))).continuous
    have i2 : Integrable (fun x => Real.exp x * a.1 x) :=
      hi _ (ivA₀_cs ha) (ivA₀_smooth ha).continuous
    rw [integral_sub i1 i2, iv_exp_ibp ha, sub_self]

/-- **I4**: `𝒜₀ = C_c^∞((0,1))` is not a core for the Friedrichs generator: ESA (F10) fails. -/
theorem iv_not_esaProp : ¬ ivDiff.ESAProp := by
  intro hesa
  obtain ⟨u, hu0, horth⟩ := iv_exp_orth
  set S := DiffusionTriple.formData ivDiff with hS
  obtain ⟨h, hG⟩ := S.generator_R u
  have hG' : (ivDiff.generator ⟨S.R u, h⟩ : Lp ℝ 2 ivμ) = S.R u - u := hG
  obtain ⟨a, ha1, ha2⟩ := hesa (S.R u) h
  have hlim : Tendsto (fun n => inner ℝ u (ivDiff.Lcls (a n) - ivDiff.cls (a n))) atTop
      (𝓝 (inner ℝ u (ivDiff.generator ⟨S.R u, h⟩ - S.R u))) :=
    tendsto_const_nhds.inner (ha2.sub ha1)
  simp only [horth] at hlim
  have h0 := tendsto_nhds_unique hlim tendsto_const_nhds
  rw [hG', sub_sub_cancel_left, inner_neg_right, neg_eq_zero, real_inner_self_eq_norm_sq] at h0
  exact hu0 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h0.symm.symm))

/-- **I4**: no `FullTriple` structure has `ivDiff` as underlying diffusion triple. -/
theorem iv_no_fullTriple (T : FullTriple ℝ) : T.toDiffusionTriple ≠ ivDiff := by
  intro h
  exact iv_not_esaProp (h ▸ T.esaProp)

end MarkovTriple.BGL.Instances.Interval
