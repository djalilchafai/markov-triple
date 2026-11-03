import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticDiffQuot

/-!
# Difference quotients are bounded by the weak derivative (R16, elliptic half; Evans §5.8.2 Thm 3(i))

Statements Q3a–Q3 of `STATEMENTS_R16_Elliptic.md` (continuation).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- **Q3a** Cauchy–Schwarz for `L²` functions. -/
lemma abs_integral_mul_le {u v : (Fin d → ℝ) → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    |∫ x, u x * v x| ≤ (eLpNorm u 2 volume).toReal * (eLpNorm v 2 volume).toReal := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  rw [← inner_toLp hu hv]
  refine (abs_real_inner_le_norm _ _).trans ?_
  simp only [Lp.norm_toLp]
  exact le_rfl

/-- translation of a test function -/
lemma contDiff_translate {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) (c : Fin d → ℝ) : Sm (fun z => φ (z - c)) :=
  hφ.comp (contDiff_id.sub contDiff_const)

lemma hasCompactSupport_translate {φ : (Fin d → ℝ) → ℝ} (hs : HasCompactSupport φ) (c : Fin d → ℝ) :
    HasCompactSupport (fun z => φ (z - c)) := hs.comp_homeomorph (Homeomorph.subRight c)

lemma fderiv_translate {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) (c z : Fin d → ℝ) :
    fderiv ℝ (fun z => φ (z - c)) z = fderiv ℝ φ (z - c) := by
  have h1 : HasFDerivAt φ (fderiv ℝ φ (z - c)) (z - c) := (hφ.differentiableAt _).hasFDerivAt
  have h2 : HasFDerivAt (fun z : Fin d → ℝ => z - c) (ContinuousLinearMap.id ℝ _) z :=
    (hasFDerivAt_id z).sub_const c
  have := h1.comp z h2
  simp only [ContinuousLinearMap.comp_id] at this
  exact this.fderiv

/-- **Q3b** the weak derivative of a translate -/
lemma weakDeriv_translate {f g : (Fin d → ℝ) → ℝ} {i : Fin d} (h : WeakDeriv f g i)
    {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) (hs : HasCompactSupport φ) (c : Fin d → ℝ) :
    ∫ z, f z * fderiv ℝ φ (z - c) (Pi.single i 1) = - ∫ z, g z * φ (z - c) := by
  have := h.2.2 (fun z => φ (z - c)) (contDiff_translate hφ c) (hasCompactSupport_translate hs c)
  simpa [fderiv_translate hφ c] using this

/-- **Q3c** an `L²` function with a dual bound on test functions has `L²` norm at most the bound. -/
lemma norm_le_of_dual_bound {G : (Fin d → ℝ) → ℝ} (hG : MemLp G 2 volume) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ φ : (Fin d → ℝ) → ℝ, Sm φ → HasCompactSupport φ →
      |∫ x, G x * φ x| ≤ M * (eLpNorm φ 2 volume).toReal) :
    (eLpNorm G 2 volume).toReal ≤ M := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set g0 : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) := hG.toLp G with hg0
  have hclosed : IsClosed {ψ : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) | |inner ℝ g0 ψ| ≤ M * ‖ψ‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hdense := Lp.dense_hasCompactSupport_contDiff (E := Fin d → ℝ) (F := ℝ) (μ := volume)
    (p := 2) (by simp)
  have hsub : {f : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) | ∃ (g : (Fin d → ℝ) → ℝ), f =ᵐ[volume] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g} ⊆
      {ψ | |inner ℝ g0 ψ| ≤ M * ‖ψ‖} := by
    rintro ψ ⟨φ, hψφ, hcs, hsm⟩
    have hφm : MemLp φ 2 volume := hsm.continuous.memLp_of_hasCompactSupport hcs
    have e : ψ = hφm.toLp φ := by
      refine Lp.ext ?_
      filter_upwards [hψφ, hφm.coeFn_toLp] with x h1 h2 using h1.trans h2.symm
    show |inner ℝ g0 ψ| ≤ M * ‖ψ‖
    rw [e, hg0, inner_toLp hG hφm, Lp.norm_toLp]
    exact hb φ hsm hcs
  have hmem : g0 ∈ {ψ : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) | |inner ℝ g0 ψ| ≤ M * ‖ψ‖} := by
    have : g0 ∈ closure {f : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) | ∃ (g : (Fin d → ℝ) → ℝ),
        f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g} := by
      rw [hdense.closure_eq]; trivial
    exact (closure_minimal hsub hclosed) this
  have h1 : ‖g0‖ * ‖g0‖ ≤ M * ‖g0‖ := by
    have := hmem
    simp only [Set.mem_ofPred_eq, real_inner_self_eq_norm_sq] at this
    rw [abs_of_nonneg (by positivity)] at this
    nlinarith [this]
  have hn : ‖g0‖ = (eLpNorm G 2 volume).toReal := by rw [hg0, Lp.norm_toLp]
  rw [← hn]
  by_cases h0 : ‖g0‖ = 0
  · rw [h0]; exact hM
  · exact le_of_mul_le_mul_right h1 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))

/-- derivative of `s ↦ ∫ f(z) φ(z − s v) dz` (differentiation under the integral sign) -/
lemma hasDerivAt_shift_integral {f φ : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) (hφ : Sm φ)
    (hs : HasCompactSupport φ) (v : Fin d → ℝ) {s0 : ℝ} (hs0 : |s0| ≤ 1) :
    HasDerivAt (fun s : ℝ => ∫ z, f z * φ (z - s • v))
      (∫ z, f z * (-(fderiv ℝ φ (z - s0 • v) v))) s0 := by
  set K : Set (Fin d → ℝ) := Metric.cthickening (2 * ‖v‖) (tsupport φ) with hK
  have hKc : IsCompact K := hs.cthickening
  obtain ⟨M, hM⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hs.fderiv (𝕜 := ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hcφ : ∀ s : ℝ, Continuous (fun z => φ (z - s • v)) := fun s => hφ.continuous.comp (continuous_id.sub continuous_const)
  have hcd : ∀ s : ℝ, Continuous (fun z => fderiv ℝ φ (z - s • v) v) := fun s =>
    ((hφ.continuous_fderiv (by simp)).comp (continuous_id.sub continuous_const)).clm_apply continuous_const
  have hsup : ∀ s : ℝ, |s| < 2 → ∀ z, z ∉ K → fderiv ℝ φ (z - s • v) v = 0 := by
    intro s hs2 z hz
    by_contra hne
    have : fderiv ℝ φ (z - s • v) ≠ 0 := fun h0 => hne (by simp [h0])
    have hmem : z - s • v ∈ tsupport φ := support_fderiv_subset ℝ this
    refine hz (Metric.mem_cthickening_of_dist_le z (z - s • v) (2 * ‖v‖) (tsupport φ) hmem ?_)
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hs2.le (norm_nonneg _)
  have hfK : IntegrableOn f K := hf.integrableOn_isCompact hKc
  have hb : Integrable (fun z => K.indicator (fun z => ‖f z‖ * (M * ‖v‖)) z) :=
    (integrable_indicator_iff hKc.measurableSet).2 (hfK.norm.mul_const _)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Fin d → ℝ)))
    (F := fun (s : ℝ) z => f z * φ (z - s • v)) (x₀ := s0) (s := Metric.ball s0 1)
    (F' := fun (s : ℝ) z => f z * (-(fderiv ℝ φ (z - s • v) v)))
    (bound := fun z => K.indicator (fun z => ‖f z‖ * (M * ‖v‖)) z)
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun s => hf.aestronglyMeasurable.mul (hcφ s).aestronglyMeasurable)
    (integrable_mul_cs hf (hcφ s0) (hasCompactSupport_translate hs (s0 • v)))
    (hf.aestronglyMeasurable.mul (hcd s0).neg.aestronglyMeasurable)
    (Eventually.of_forall fun z s hsb => by
      have hs2 : |s| < 2 := by
        have := Metric.mem_ball.1 hsb
        rw [Real.dist_eq] at this
        calc |s| = |s - s0 + s0| := by ring_nf
          _ ≤ |s - s0| + |s0| := abs_add_le _ _
          _ < 2 := by linarith
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz, norm_mul, norm_neg]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖fderiv ℝ φ (z - s • v) v‖ ≤ ‖fderiv ℝ φ (z - s • v)‖ * ‖v‖ := (fderiv ℝ φ _).le_opNorm v
          _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hz, hsup s hs2 z hz]; simp)
    hb
    (Eventually.of_forall fun z s _ => by
      have h1 : HasDerivAt (fun s : ℝ => z - s • v) (-v) s := by
        simpa using ((hasDerivAt_id s).smul_const v).const_sub z
      have h2 : HasFDerivAt φ (fderiv ℝ φ (z - s • v)) (z - s • v) := (hφ.differentiableAt _).hasFDerivAt
      have := (h2.comp_hasDerivAt s h1).const_mul (f z)
      simpa using this)
  exact this.2

/-- the `L²` norm is translation invariant -/
lemma eLpNorm_translate {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) (c : Fin d → ℝ) :
    eLpNorm (fun z => φ (z - c)) 2 volume = eLpNorm φ 2 volume := by
  have := eLpNorm_comp_measurePreserving (p := 2) (g := φ) hφ.aestronglyMeasurable
    (measurePreserving_sub_right (volume : Measure (Fin d → ℝ)) c)
  exact this

/-- **Q3** (Evans §5.8.2 Thm 3(i)): `‖D_h f‖₂ ≤ ‖∂ᵢ f‖₂`. -/
theorem eLpNorm_dq_le {f g : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) {i : Fin d}
    (hw : WeakDeriv f g i) (h : ℝ) : eLpNorm (dq i h f) 2 volume ≤ eLpNorm g 2 volume := by
  by_cases h0 : h = 0
  · have : dq i h f = 0 := by funext x; simp [dq, h0]
    rw [this]; simp
  have hG := memLp_dq hf i h
  have hloc : LocallyIntegrable f := hf.locallyIntegrable (by norm_num)
  set v : Fin d → ℝ := h • Pi.single i 1 with hv
  have key := norm_le_of_dual_bound hG (M := (eLpNorm g 2 volume).toReal) ENNReal.toReal_nonneg
    (fun φ hφ hs => ?_)
  · exact (ENNReal.toReal_le_toReal hG.eLpNorm_ne_top hg.eLpNorm_ne_top).1 key
  · have hφm : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
    set C : ℝ := |h| * ((eLpNorm g 2 volume).toReal * (eLpNorm φ 2 volume).toReal) with hC
    have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => ∫ z, f z * φ (z - s • v))
        (h * ∫ z, g z * φ (z - s • v)) (Set.Icc 0 1) s := by
      intro s hs1
      have hs0 : |s| ≤ 1 := by rw [abs_of_nonneg hs1.1]; exact hs1.2
      have := hasDerivAt_shift_integral hloc hφ hs v hs0
      have e : ∫ z, f z * (-(fderiv ℝ φ (z - s • v) v)) = h * ∫ z, g z * φ (z - s • v) := by
        have e1 : ∀ z, f z * (-(fderiv ℝ φ (z - s • v) v)) =
            -h * (f z * fderiv ℝ φ (z - s • v) (Pi.single i 1)) := by
          intro z; rw [hv, map_smul, smul_eq_mul]; ring
        simp_rw [e1]
        rw [integral_const_mul, weakDeriv_translate hw hφ hs (s • v)]
        ring
      rw [e] at this
      exact this.hasDerivWithinAt
    have hbd : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖h * ∫ z, g z * φ (z - s • v)‖ ≤ C := by
      intro s _
      rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hψ : MemLp (fun z => φ (z - s • v)) 2 volume := by
        have := hφm.comp_measurePreserving (measurePreserving_sub_right (volume : Measure (Fin d → ℝ)) (s • v))
        exact this
      have := abs_integral_mul_le hg hψ
      rwa [eLpNorm_translate hφ.continuous] at this
    have mvt := norm_image_sub_le_of_norm_deriv_le_segment' hder hbd 1 (Set.right_mem_Icc.2 zero_le_one)
    -- identify `F 1 − F 0` with `h ∫ D_h f · φ`
    have hφv : Continuous (fun y => φ (y - v)) := hφ.continuous.comp (continuous_id.sub continuous_const)
    have I1 : Integrable (fun y => f y * φ (y - v)) :=
      integrable_mul_cs hloc hφv (hasCompactSupport_translate hs v)
    have I2 : Integrable (fun y => f y * φ y) := integrable_mul_cs hloc hφ.continuous hs
    have hibp := dq_ibp hloc hφ.continuous hs i h
    have e2 : ∫ x, f x * dq i (-h) φ x = -(h⁻¹ * ((∫ y, f y * φ (y - v)) - ∫ y, f y * φ y)) := by
      rw [← integral_sub I1 I2, ← integral_const_mul, ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [dq, neg_smul, ← hv, sub_eq_add_neg, div_neg]
      ring
    have e3 : ∫ x, dq i h f x * φ x = h⁻¹ * ((∫ y, f y * φ (y - v)) - ∫ y, f y * φ y) := by
      rw [hibp, e2]; ring
    have mvt' : |(∫ z, f z * φ (z - (1 : ℝ) • v)) - ∫ z, f z * φ (z - (0 : ℝ) • v)| ≤ C := by
      have := mvt
      simpa [Real.norm_eq_abs] using this
    simp only [one_smul, zero_smul, sub_zero] at mvt'
    rw [e3, abs_mul, abs_inv]
    have hh : 0 < |h| := abs_pos.2 h0
    rw [inv_mul_le_iff₀ hh]
    calc |(∫ y, f y * φ (y - v)) - ∫ y, f y * φ y| ≤ C := mvt'
      _ = |h| * ((eLpNorm g 2 volume).toReal * (eLpNorm φ 2 volume).toReal) := hC
      _ = _ := by ring

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
