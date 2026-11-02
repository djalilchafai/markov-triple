import MarkovTriple.BGL.Analysis.OU.Energy
import MarkovTriple.BGL.Analysis.Circle.Modes

/-! # OU (Part 11): abstract semigroup lemmas (eigenvectors of the closure) -/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

section Abstract

open MarkovTriple.Sanity.Circle (IsSG)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable {P : ℝ≥0 → H →L[ℝ] H}

lemma toNNReal_nhdsGT (x : ℝ) : Tendsto (fun s : ℝ => s - x) (𝓝[>] x) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun s : ℝ => s - x) (𝓝 x) (𝓝 (x - x)) :=
      (continuous_id.sub continuous_const).tendsto x
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_pos.2 (show x < s from hs)

omit [CompleteSpace H] in
/-- the orbit of a generator-domain vector has right derivative `P x v` -/
lemma hasDerivWithinAt_orbit (hP : IsSG P) {u v : H}
    (hgen : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (𝓝[>] 0) (𝓝 v))
    {x : ℝ} (hx0 : 0 ≤ x) :
    HasDerivWithinAt (fun s : ℝ => P s.toNNReal u) (P x.toNNReal v) (Ioi x) x := by
  have hQ : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → P (a + b).toNNReal = (P a.toNNReal).comp (P b.toNNReal) := by
    intro a b ha hb
    rw [Real.toNNReal_add ha hb, hP.add]
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have hT : Tendsto Real.toNNReal (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ≥0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := continuous_real_toNNReal.tendsto (0:ℝ)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact Real.toNNReal_pos.2 hh
  have h1 : Tendsto (fun h : ℝ => h⁻¹ • (P h.toNNReal u - u)) (𝓝[>] 0) (𝓝 v) := by
    refine (hgen.comp hT).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp [Real.coe_toNNReal _ (le_of_lt (show (0:ℝ) < h from hh))]
  have h3 := ((P x.toNNReal).continuous.tendsto _).comp (h1.comp (toNNReal_nhdsGT x))
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : x < s := hs
  have hsx : 0 ≤ s - x := (sub_pos.2 hs').le
  have e1 : P s.toNNReal u = P x.toNNReal (P (s - x).toNNReal u) := by
    have : s = x + (s - x) := by ring
    conv_lhs => rw [this]
    rw [hQ hx0 hsx]; rfl
  simp only [Function.comp, slope_def_module, map_smul, map_sub]
  rw [e1]

/-- integral formula for a generator-domain vector -/
lemma orbit_integral (hP : IsSG P) {u v : H}
    (hgen : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (𝓝[>] 0) (𝓝 v)) (t : ℝ≥0) :
    P t u - u = ∫ s in (0:ℝ)..(t : ℝ), P s.toNNReal v := by
  have hcontv : Continuous fun s : ℝ => P s.toNNReal v :=
    (hP.continuous_apply v).comp continuous_real_toNNReal
  have hcontu : Continuous fun s : ℝ => P s.toNNReal u :=
    (hP.continuous_apply u).comp continuous_real_toNNReal
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := 0) (b := (t : ℝ))
    (f := fun s : ℝ => P s.toNNReal u) (f' := fun s : ℝ => P s.toNNReal v) t.2
    hcontu.continuousOn (fun x hx => hasDerivWithinAt_orbit hP hgen hx.1.le)
    (hcontv.intervalIntegrable _ _)
  rw [this]
  simp [hP.zero]

/-- integral formula for a vector in the closure (graph-norm limit) -/
lemma closure_integral (hP : IsSG P) {e w : H} {u v : ℕ → H}
    (hgen : ∀ k, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t (u k) - u k)) (𝓝[>] 0) (𝓝 (v k)))
    (hu : Tendsto u atTop (𝓝 e)) (hv : Tendsto v atTop (𝓝 w)) (t : ℝ≥0) :
    P t e - e = ∫ s in (0:ℝ)..(t : ℝ), P s.toNNReal w := by
  have hcont : ∀ z : H, Continuous fun s : ℝ => P s.toNNReal z := fun z =>
    (hP.continuous_apply z).comp continuous_real_toNNReal
  have hL : Tendsto (fun k => P t (u k) - u k) atTop (𝓝 (P t e - e)) :=
    (((P t).continuous.tendsto e).comp hu).sub hu
  obtain ⟨M, hM⟩ := hP.bound_upto t
  have hR : Tendsto (fun k => ∫ s in (0:ℝ)..(t : ℝ), P s.toNNReal (v k)) atTop
      (𝓝 (∫ s in (0:ℝ)..(t : ℝ), P s.toNNReal w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖(∫ s in (0:ℝ)..(t : ℝ), P s.toNNReal (v k)) -
        ∫ s in (0:ℝ)..(t : ℝ), P s.toNNReal w‖ ≤ M * (t : ℝ) * ‖v k - w‖ := by
      intro k
      rw [← intervalIntegral.integral_sub ((hcont _).intervalIntegrable _ _)
        ((hcont _).intervalIntegrable _ _)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
        (f := fun s : ℝ => P s.toNNReal (v k) - P s.toNNReal w) (C := M * ‖v k - w‖)
        (fun s hs => by
          have hs' : s ∈ Ioc (0:ℝ) t := by simpa [uIoc_of_le t.2] using hs
          have : s.toNNReal ≤ t := by
            rw [Real.toNNReal_le_iff_le_coe]; exact hs'.2
          rw [← map_sub]
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hM _ this) (norm_nonneg _)))
      simp only [sub_zero, NNReal.abs_eq] at this
      calc _ ≤ M * ‖v k - w‖ * t := this
        _ = _ := by ring
    have hz : Tendsto (fun k => M * (t : ℝ) * ‖v k - w‖) atTop (𝓝 0) := by
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 hv).const_mul (M * (t : ℝ)))
      simpa using this
    exact squeeze_zero (fun k => norm_nonneg _) hb hz
  have heq : ∀ k, P t (u k) - u k = ∫ s in (0:ℝ)..(t : ℝ), P s.toNNReal (v k) :=
    fun k => orbit_integral hP (hgen k) t
  have hL' : Tendsto (fun k => ∫ s in (0:ℝ)..(t : ℝ), P s.toNNReal (v k)) atTop (𝓝 (P t e - e)) :=
    hL.congr heq
  exact tendsto_nhds_unique hL' hR

/-- **eigenvectors of the closure are eigenvectors of every semigroup extending the generator on a
core** (the Hermite polynomials are not in `C_c^∞`, but are graph-limits of test functions). -/
theorem eigen_of_closure (hP : IsSG P) (c : ℝ) {e : H} {u v : ℕ → H}
    (hgen : ∀ k, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t (u k) - u k)) (𝓝[>] 0) (𝓝 (v k)))
    (hu : Tendsto u atTop (𝓝 e)) (hv : Tendsto v atTop (𝓝 ((-c) • e))) (t : ℝ≥0) :
    P t e = Real.exp (-c * t) • e := by
  have hcont : Continuous fun s : ℝ => P s.toNNReal e :=
    (hP.continuous_apply e).comp continuous_real_toNNReal
  have hint := closure_integral hP hgen hu hv
  have hint' : ∀ s : ℝ≥0, P s e = e + (-c) • ∫ r in (0:ℝ)..(s : ℝ), P r.toNNReal e := by
    intro s
    have := hint s
    have h2 : ∫ r in (0:ℝ)..(s : ℝ), P r.toNNReal ((-c) • e) =
        (-c) • ∫ r in (0:ℝ)..(s : ℝ), P r.toNNReal e := by
      simp_rw [map_smul]
      exact intervalIntegral.integral_smul _ _
    rw [h2] at this
    rw [← this]; abel
  set y : ℝ → H := fun s => P s.toNNReal e with hy
  have hyd : ∀ x : ℝ, 0 ≤ x → HasDerivWithinAt y ((-c) • y x) (Ioi x) x := by
    intro x hx
    have hI : HasDerivWithinAt (fun u : ℝ => ∫ r in (0:ℝ)..u, y r) (y x) (Ici x) x :=
      intervalIntegral.integral_hasDerivWithinAt_right (hcont.intervalIntegrable _ _)
        (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousWithinAt
    have h2 := (hI.const_smul (-c)).const_add e
    refine (h2.mono Ioi_subset_Ici_self).congr (fun s hs => ?_) ?_
    · have hs0 : 0 ≤ s := hx.trans (le_of_lt hs)
      have := hint' s.toNNReal
      simp only [Real.coe_toNNReal _ hs0] at this
      simpa [hy] using this
    · have := hint' x.toNNReal
      simp only [Real.coe_toNNReal _ hx] at this
      simpa [hy] using this
  set φ : ℝ → H := fun s => Real.exp (c * s) • y s with hφ
  have hderiv : ∀ x ∈ Ico (0:ℝ) t, HasDerivWithinAt φ 0 (Ici x) x := by
    intro x hx
    have hexp : HasDerivWithinAt (fun s : ℝ => Real.exp (c * s)) (Real.exp (c * x) * c) (Ioi x) x := by
      have := ((hasDerivAt_id x).const_mul c).exp
      simpa using this.hasDerivWithinAt
    have := hexp.smul (hyd x hx.1)
    have h0 : HasDerivWithinAt φ 0 (Ioi x) x := by
      refine this.congr_deriv ?_
      rw [smul_smul, ← add_smul]
      have : Real.exp (c * x) * -c + Real.exp (c * x) * c = 0 := by ring
      rw [this, zero_smul]
    exact h0.Ici_of_Ioi
  have hcont' : ContinuousOn φ (Icc 0 (t : ℝ)) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul hcont).continuousOn
  have := constant_of_has_deriv_right_zero hcont' hderiv (t : ℝ) ⟨t.2, le_rfl⟩
  have h00 : φ 0 = e := by simp [hφ, hy, hP.zero]
  rw [h00] at this
  simp only [hφ, hy, Real.toNNReal_coe] at this
  have e2 : P t e = Real.exp (-c * t) • (Real.exp (c * t) • P t e) := by
    rw [smul_smul, ← Real.exp_add]; simp
  rw [e2, this]

end Abstract

end MarkovTriple.Sanity.OU
