import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticWeakForm

/-!
# Preliminaries for interior `H²` regularity (R16, elliptic half; Evans §6.3.1 Step 1, §5.8.2)

* `locallyIntegrable_translate`;
* `weakDeriv_dq`: difference quotients commute with weak derivatives (`D_h ∂ⱼ f = ∂ⱼ D_h f`);
* `dq_ibp_L2`: `∫ D_h F · Ψ = − ∫ F · D_{−h} Ψ` for `F ∈ L²_loc`, `Ψ ∈ L²` with compact support;
* `dq_local_bound`: `‖D_h f‖_{L²(K)} ≤ C_K` for `|h| ≤ 1` when `f, ∂ᵢ f ∈ L²_loc` (Evans §5.8.2 Thm 3(i), local form).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

lemma locallyIntegrable_translate {f : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) (c : Fin d → ℝ) :
    LocallyIntegrable (fun x => f (x + c)) := by
  have h := (locallyIntegrable_map_homeomorph (μ := (volume : Measure (Fin d → ℝ)))
    (Homeomorph.addRight c) (f := f)).1
  have hm : Measure.map (Homeomorph.addRight c) (volume : Measure (Fin d → ℝ)) = volume :=
    map_add_right_eq_self _ c
  rw [hm] at h
  exact h hf

lemma locallyIntegrable_dq {f : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) (i : Fin d) (t : ℝ) :
    LocallyIntegrable (dq i t f) := by
  have := ((locallyIntegrable_translate hf (t • Pi.single i 1)).sub hf).smul t⁻¹
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp [dq, div_eq_inv_mul]

lemma contDiff_dq {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) (i : Fin d) (t : ℝ) : Sm (dq i t φ) := by
  unfold dq
  exact ((hφ.comp (contDiff_id.add contDiff_const)).sub hφ).div_const t

lemma hasCompactSupport_dq {φ : (Fin d → ℝ) → ℝ} (hs : HasCompactSupport φ) (i : Fin d) (t : ℝ) :
    HasCompactSupport (dq i t φ) := by
  unfold dq
  have h1 : HasCompactSupport (fun x => φ (x + t • Pi.single i 1)) :=
    hs.comp_homeomorph (Homeomorph.addRight (t • Pi.single i 1))
  have h2 : HasCompactSupport (fun x => φ (x + t • (Pi.single i 1 : Fin d → ℝ)) + -φ x) := h1.add hs.neg
  refine HasCompactSupport.intro h2 fun x hx => ?_
  have := image_eq_zero_of_notMem_tsupport hx
  show (φ (x + t • (Pi.single i 1 : Fin d → ℝ)) - φ x) / t = 0
  have h3 : φ (x + t • (Pi.single i 1 : Fin d → ℝ)) - φ x = 0 := by simpa [sub_eq_add_neg] using this
  rw [h3, zero_div]

lemma fderiv_dq {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) (i : Fin d) (t : ℝ) (x : Fin d → ℝ) :
    fderiv ℝ (dq i t φ) x =
      t⁻¹ • (fderiv ℝ φ (x + t • Pi.single i 1) - fderiv ℝ φ x) := by
  have h1 : HasFDerivAt (fun x => φ (x + t • (Pi.single i 1 : Fin d → ℝ)))
      (fderiv ℝ φ (x + t • Pi.single i 1)) x := by
    have := ((hφ.differentiableAt (x + t • Pi.single i 1)).hasFDerivAt).comp x
      ((hasFDerivAt_id x).add_const (t • (Pi.single i 1 : Fin d → ℝ)))
    exact this
  have h2 : HasFDerivAt φ (fderiv ℝ φ x) x := (hφ.differentiableAt x).hasFDerivAt
  have h3 := ((h1.sub h2).const_smul t⁻¹)
  have e : dq i t φ = fun x => t⁻¹ • (φ (x + t • (Pi.single i 1 : Fin d → ℝ)) - φ x) := by
    funext y; simp [dq, div_eq_inv_mul]
  rw [e]
  exact h3.fderiv

/-- **D1** difference quotients commute with weak derivatives -/
theorem weakDeriv_dq {f g : (Fin d → ℝ) → ℝ} {j : Fin d} (h : WeakDeriv f g j) (k : Fin d) (t : ℝ) :
    WeakDeriv (dq k t f) (dq k t g) j := by
  refine ⟨locallyIntegrable_dq h.1 k t, locallyIntegrable_dq h.2.1 k t, fun φ hφ hs => ?_⟩
  have hφS : Sm φ := hφ
  have hd : Continuous (fun x => fderiv ℝ φ x (Pi.single j 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x => fderiv ℝ φ x (Pi.single j 1)) := hs.fderiv_apply ℝ (Pi.single j 1)
  have e1 := dq_ibp h.1 hd hdc k t
  have hcomm : ∀ x, fderiv ℝ (dq k (-t) φ) x (Pi.single j 1) =
      dq k (-t) (fun x => fderiv ℝ φ x (Pi.single j 1)) x := by
    intro x
    rw [fderiv_dq hφS k (-t) x]
    simp only [smul_apply, sub_apply, smul_eq_mul, dq]
    rw [div_eq_inv_mul]
  have e2 := h.2.2 (dq k (-t) φ) (contDiff_dq hφS k (-t)) (hasCompactSupport_dq hs k (-t))
  have e3 := dq_ibp h.2.1 hφS.continuous hs k t
  simp only [hcomm] at e2
  rw [e1, e2, e3]

lemma integrable_locL2_mul_cs {F Ψ : (Fin d → ℝ) → ℝ} (hF : LocL2 F) (hΨ : MemLp Ψ 2 volume)
    (hs : HasCompactSupport Ψ) : Integrable (fun x => F x * Ψ x) := by
  have hS : IsCompact (tsupport Ψ) := hs
  have h1 : MemLp ((tsupport Ψ).indicator F) 2 volume := LocL2.memLp_indicator hF hS
  have := h1.integrable_mul hΨ
  refine this.congr (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport Ψ
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport hx]

/-- integration by parts for difference quotients, `L²` test functions -/
theorem dq_ibp_L2 {F Ψ : (Fin d → ℝ) → ℝ} (hF : LocL2 F) (hΨ : MemLp Ψ 2 volume)
    (hs : HasCompactSupport Ψ) (i : Fin d) (h : ℝ) :
    ∫ x, dq i h F x * Ψ x = - ∫ x, F x * dq i (-h) Ψ x := by
  set v : Fin d → ℝ := h • Pi.single i 1 with hv
  have hΨv : MemLp (fun y => Ψ (y - v)) 2 volume :=
    hΨ.comp_measurePreserving (measurePreserving_sub_right (volume : Measure (Fin d → ℝ)) v)
  have hsv : HasCompactSupport (fun y => Ψ (y - v)) := hs.comp_homeomorph (Homeomorph.subRight v)
  have I1 : Integrable (fun y => F y * Ψ (y - v)) := integrable_locL2_mul_cs hF hΨv hsv
  have I2 : Integrable (fun y => F y * Ψ y) := integrable_locL2_mul_cs hF hΨ hs
  have I3 : Integrable (fun x => F (x + v) * Ψ x) := by
    have := I1.comp_add_right v
    simpa using this
  have E1 : ∫ x, F (x + v) * Ψ x = ∫ y, F y * Ψ (y - v) := by
    have := integral_add_right_eq_self (μ := (volume : Measure (Fin d → ℝ))) (fun y => F y * Ψ (y - v)) v
    simpa using this
  have lhs : ∫ x, dq i h F x * Ψ x = h⁻¹ * ((∫ y, F y * Ψ (y - v)) - ∫ y, F y * Ψ y) := by
    rw [← E1, ← integral_sub I3 I2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dq, ← hv]; ring
  have rhs : ∫ x, F x * dq i (-h) Ψ x = - (h⁻¹ * ((∫ y, F y * Ψ (y - v)) - ∫ y, F y * Ψ y)) := by
    rw [← integral_sub I1 I2, ← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dq, neg_smul, ← hv, sub_eq_add_neg, div_neg]
    ring
  rw [lhs, rhs]; ring

lemma memLp_of_locL2_cs {f : (Fin d → ℝ) → ℝ} (hf : LocL2 f) (hs : HasCompactSupport f) : MemLp f 2 volume := by
  have h1 : MemLp ((tsupport f).indicator f) 2 volume := LocL2.memLp_indicator hf hs
  have h2 : f = (tsupport f).indicator f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · simp [hx]
    · simp [hx, image_eq_zero_of_notMem_tsupport hx]
  rwa [← h2] at h1

/-- **D2** local form of Evans §5.8.2 Thm 3(i): for `|t| ≤ 1`, `‖D_t f‖_{L²(K)}` is bounded in terms of `f, ∂ᵢf`. -/
theorem dq_local_bound {f g : (Fin d → ℝ) → ℝ} (hf : LocL2 f) (hg : LocL2 g) {i : Fin d}
    (hw : WeakDeriv f g i) {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 1 → eLpNorm (dq i t f) 2 (volume.restrict K) ≤ ENNReal.ofReal C := by
  obtain ⟨R, hR⟩ := exists_ball_of_compact (hK.cthickening (r := 1))
  set ζ : (Fin d → ℝ) → ℝ := cut ((R : ℝ) + 1) with hζ
  have hζs : Sm ζ := sm_cut _
  have hζc : HasCompactSupport ζ := hcs_cut (by positivity)
  have hζ1 : ∀ x ∈ Metric.cthickening 1 K, ζ x = 1 := fun x hx =>
    cut_eq_one (by positivity) (by nlinarith [hR x hx, Nat.cast_nonneg (α := ℝ) R])
  set F : (Fin d → ℝ) → ℝ := fun x => ζ x * f x with hF
  have hFw : WeakDeriv F (fun x => ζ x * g x + pderiv ζ i x * f x) i := hw.smooth_mul hζs
  have hFL : LocL2 F := LocL2.mul_continuous hf hζs.continuous
  have hFc : HasCompactSupport F := HasCompactSupport.intro hζc fun x hx => by
    simp [hF, image_eq_zero_of_notMem_tsupport hx]
  have hFm : MemLp F 2 volume := memLp_of_locL2_cs hFL hFc
  have hGL : LocL2 (fun x => ζ x * g x + pderiv ζ i x * f x) :=
    (LocL2.mul_continuous hg hζs.continuous).add (LocL2.mul_continuous hf (hζs.pderiv i).continuous)
  have hGc : HasCompactSupport (fun x => ζ x * g x + pderiv ζ i x * f x) :=
    HasCompactSupport.intro hζc fun x hx => by
      have h0 : ζ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have h1 : pderiv ζ i x = 0 := by
        have : fderiv ℝ ζ x = 0 := by
          by_contra hne; exact hx (support_fderiv_subset ℝ hne)
        simp [pderiv, this]
      simp [h0, h1]
  have hGm := memLp_of_locL2_cs hGL hGc
  refine ⟨(eLpNorm (fun x => ζ x * g x + pderiv ζ i x * f x) 2 volume).toReal, ENNReal.toReal_nonneg,
    fun t ht => ?_⟩
  have h1 := eLpNorm_dq_le hFm hGm hFw t
  have h2 : eLpNorm (dq i t f) 2 (volume.restrict K) = eLpNorm (dq i t F) 2 (volume.restrict K) := by
    refine eLpNorm_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hK.measurableSet]
    refine Eventually.of_forall fun x hx => ?_
    have hx1 : ζ x = 1 := hζ1 x (Metric.self_subset_cthickening _ hx)
    have hx2 : ζ (x + t • Pi.single i 1) = 1 := by
      refine hζ1 _ (Metric.mem_cthickening_of_dist_le _ x 1 K hx ?_)
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (norm_single_le i)).trans ht
    simp [dq, hF, hx1, hx2]
  rw [h2, ENNReal.ofReal_toReal hGm.eLpNorm_ne_top]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans h1

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
