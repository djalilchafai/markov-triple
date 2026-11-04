import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.Prim

/-!
# Regularity of weak solutions of `(L - 1) u = 0` on `(-1,1)` (step (i) of `STATEMENTS_R23_G1.md`)

`u ∈ L²(W dx)` with `∫ u W (f - L f) dx = 0` for all `f ∈ C_c^∞((-1,1))` coincides a.e. with a `v` with `v' = F/p`, `F' = W v`
(classical derivatives on `(-1,1)`), `p = (1-x²)²`, `W = 1-x²`.  Proof: with `k = W u`, `H = ∫₀ˣ k`, the weak equation says
`∫ (m ψ + g ψ') = 0` for mean-zero `ψ`, `g = p u`, `m = H - 4 x k`; the kernel trick removes the mean-zero condition at the cost of a
constant `c`; an absolutely continuous integration by parts and du Bois-Reymond give `g = M + e` a.e., `M = ∫₀ˣ (m - c)`; so
`u` is a.e. continuous, hence `H, M` are `C¹` and `v = (M+e)/p` satisfies the ODE.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.ESA

/-- integration by parts against the primitive, for a test function on `(-1,1)`. -/
lemma ibp_I {k : ℝ → ℝ} (hk : LocInt k) {φ : ℝ → ℝ} (hφ : φ ∈ goA₀) :
    ∫ x in Ioo (-1:ℝ) 1, (∫ t in (0:ℝ)..x, k t) * deriv φ x =
      - ∫ x in Ioo (-1:ℝ) 1, k x * φ x := by
  obtain ⟨r₁, h01, h11, hr1⟩ := exists_Icc hφ
  obtain ⟨r₂, h02, h12, hr2⟩ := exists_Icc (deriv_mem_goA₀ hφ)
  set r := max r₁ r₂ with hr
  set R := (r + 1) / 2 with hR
  have hr0 : 0 ≤ r := h01.trans (le_max_left _ _)
  have hr1' : r < 1 := max_lt h11 h12
  have hrR : r < R := by rw [hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith
  have hR0 : 0 ≤ R := hr0.trans hrR.le
  have hφz : ∀ x, R < |x| → φ x = 0 := fun x hx =>
    hr1 x (lt_of_le_of_lt (le_max_left _ _) (hrR.trans hx))
  have hdz : ∀ x, R < |x| → deriv φ x = 0 := fun x hx =>
    hr2 x (lt_of_le_of_lt (le_max_right _ _) (hrR.trans hx))
  have e1 : ∫ x in Ioo (-1:ℝ) 1, (∫ t in (0:ℝ)..x, k t) * deriv φ x =
      ∫ x in (-R)..R, (∫ t in (0:ℝ)..x, k t) * deriv φ x :=
    integral_Ioo_eq hR0 hR1 (fun x hx => by rw [hdz x hx, mul_zero])
  have e2 : ∫ x in Ioo (-1:ℝ) 1, k x * φ x = ∫ x in (-R)..R, k x * φ x :=
    integral_Ioo_eq hR0 hR1 (fun x hx => by rw [hφz x hx, mul_zero])
  have hkI : IntervalIntegrable k volume (-R) R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 (hk R hR0 hR1)
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  rw [e1, e2]
  exact ibp_primitive (by linarith) ⟨by linarith, by linarith⟩ hkI hφ1
    (hr1 (-R) (lt_of_le_of_lt (le_max_left _ _) (by rw [abs_neg, abs_of_nonneg hR0]; exact hrR)))
    (hr1 R (lt_of_le_of_lt (le_max_left _ _) (by rw [abs_of_nonneg hR0]; exact hrR)))

/-- local integrability from `L²(W dx)`. -/
lemma locInt_of_L2 {u : ℝ → ℝ} (hint : IntegrableOn (fun x => (1 - x ^ 2) * u x ^ 2) (Ioo (-1:ℝ) 1))
    (hmeas : AEStronglyMeasurable u (volume.restrict (Ioo (-1:ℝ) 1))) : LocInt u := by
  intro r h0 h1
  have hsub : Icc (-r) r ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hδ : 0 < 1 - r ^ 2 := by nlinarith
  have hI : IntegrableOn (fun x => (1 - x ^ 2) * u x ^ 2) (Icc (-r) r) := hint.mono_set hsub
  have hm : AEStronglyMeasurable u (volume.restrict (Icc (-r) r)) :=
    hmeas.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hsq : IntegrableOn (fun x => 1 + u x ^ 2) (Icc (-r) r) := by
    refine (integrableOn_const (by simp)).add ?_
    refine ((hI.const_mul (1 / (1 - r ^ 2))).mono' ?_ ?_)
    · exact (hm.pow 2 : AEStronglyMeasurable (fun x => u x ^ 2) _)
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hx2 : x ^ 2 ≤ r ^ 2 := by nlinarith [hx.1, hx.2]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h3 : 1 ≤ (1 - x ^ 2) / (1 - r ^ 2) := by
        rw [le_div_iff₀ hδ]; nlinarith
      have h4 : 1 / (1 - r ^ 2) * ((1 - x ^ 2) * u x ^ 2) = (1 - x ^ 2) / (1 - r ^ 2) * u x ^ 2 := by
        field_simp
      rw [h4]
      nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg (u x))]
  refine hsq.mono' hm ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun x _ => ?_
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|u x| - 1), sq_abs (u x), abs_nonneg (u x)]


/-- derivative of a primitive of an a.e. continuous function. -/
lemma hasDerivAt_primitive_of_ae {f f' : ℝ → ℝ} (hc : ContinuousOn f' (Ioo (-1:ℝ) 1))
    (hae : ∀ᵐ t, t ∈ Ioo (-1:ℝ) 1 → f t = f' t) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y => ∫ t in (0:ℝ)..y, f t) (f' x) x := by
  have h0 : (0:ℝ) ∈ Ioo (-1:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hsubI : ∀ y ∈ Ioo (-1:ℝ) 1, uIcc 0 y ⊆ Ioo (-1:ℝ) 1 := fun y hy =>
    Set.ordConnected_Ioo.uIcc_subset h0 hy
  have heq : ∀ y ∈ Ioo (-1:ℝ) 1, ∫ t in (0:ℝ)..y, f t = ∫ t in (0:ℝ)..y, f' t := by
    intro y hy
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with t ht htI
    exact ht (hsubI y hy (uIoc_subset_uIcc htI))
  have hd : HasDerivAt (fun y => ∫ t in (0:ℝ)..y, f' t) (f' x) x := by
    have hint : IntervalIntegrable f' volume 0 x := (hc.mono (hsubI x hx)).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_right hint
      (hc.stronglyMeasurableAtFilter isOpen_Ioo x hx) (hc.continuousAt (isOpen_Ioo.mem_nhds hx))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using heq y hy

/-! ### the objects `k = W u`, `g = p u`, `H = ∫₀ k`, `m = H - 4 x k` -/

def wk (u : ℝ → ℝ) (x : ℝ) : ℝ := (1 - x ^ 2) * u x
def wg (u : ℝ → ℝ) (x : ℝ) : ℝ := (1 - x ^ 2) ^ 2 * u x
noncomputable def wH (u : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, wk u t
noncomputable def wm (u : ℝ → ℝ) (x : ℝ) : ℝ := wH u x - 4 * x * wk u x

lemma locInt_wk {u : ℝ → ℝ} (hu : LocInt u) : LocInt (wk u) :=
  hu.cont_mul (g := fun x => 1 - x ^ 2) (by fun_prop)

lemma locInt_wg {u : ℝ → ℝ} (hu : LocInt u) : LocInt (wg u) :=
  hu.cont_mul (g := fun x => (1 - x ^ 2) ^ 2) (by fun_prop)

lemma locInt_wH {u : ℝ → ℝ} (hu : LocInt u) : LocInt (wH u) :=
  LocInt.of_continuousOn (locInt_wk hu).continuousOn_primitive

lemma locInt_wm {u : ℝ → ℝ} (hu : LocInt u) : LocInt (wm u) :=
  (locInt_wH hu).sub ((locInt_wk hu).cont_mul (g := fun x => 4 * x) (by fun_prop))

/-- Step 1: the weak equation, in first-order form, for mean-zero test functions. -/
lemma weak_step1 {u : ℝ → ℝ} (hu : LocInt u)
    (hweak : ∀ f ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, u x * ((1 - x ^ 2) * (f x - goL f x)) = 0) :
    ∀ ψ ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, ψ x = 0 →
      ∫ x in Ioo (-1:ℝ) 1, (wm u x * ψ x + wg u x * deriv ψ x) = 0 := by
  intro ψ hψ h0
  obtain ⟨hf, hfd⟩ := primitive_mem hψ h0
  set f : ℝ → ℝ := fun x => ∫ t in (-1:ℝ)..x, ψ t with hfdef
  have h := hweak f hf
  have hk := locInt_wk hu
  have hg := locInt_wg hu
  have hH := locInt_wH hu
  have hxk : LocInt (fun x => 4 * x * wk u x) := hk.cont_mul (g := fun x => 4 * x) (by fun_prop)
  have e : ∀ x, u x * ((1 - x ^ 2) * (f x - goL f x)) =
      wk u x * f x - wg u x * deriv ψ x + (4 * x * wk u x) * ψ x := by
    intro x
    simp only [goL, hfd, wk, wg]; ring
  have i1 := integrableOn_mul_test hk hf
  have i2 := integrableOn_mul_test hg (deriv_mem_goA₀ hψ)
  have i3 := integrableOn_mul_test hxk hψ
  have i4 := integrableOn_mul_test hH hψ
  simp_rw [e] at h
  have i12 : IntegrableOn (fun x => wk u x * f x - wg u x * deriv ψ x) (Ioo (-1:ℝ) 1) := i1.sub i2
  rw [integral_add i12 i3, integral_sub i1 i2] at h
  have ibp := ibp_I hk hf
  simp only [hfd] at ibp
  have e2 : ∀ x, wm u x * ψ x + wg u x * deriv ψ x =
      wH u x * ψ x - (4 * x * wk u x) * ψ x + wg u x * deriv ψ x := by
    intro x; simp only [wm]; ring
  simp_rw [e2]
  have i43 : IntegrableOn (fun x => wH u x * ψ x - (4 * x * wk u x) * ψ x) (Ioo (-1:ℝ) 1) :=
    i4.sub i3
  rw [integral_add i43 i2, integral_sub i4 i3]
  have : ∫ x in Ioo (-1:ℝ) 1, wH u x * ψ x = -∫ x in Ioo (-1:ℝ) 1, wk u x * f x := by
    simpa [wH] using ibp
  linarith


/-- **(i) Regularity of weak solutions of `(L - 1) u = 0`** on `(-1,1)`. -/
theorem weak_regular (u : ℝ → ℝ)
    (hint : IntegrableOn (fun x => (1 - x ^ 2) * u x ^ 2) (Ioo (-1:ℝ) 1))
    (hmeas : AEStronglyMeasurable u (volume.restrict (Ioo (-1:ℝ) 1)))
    (hweak : ∀ f ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, u x * ((1 - x ^ 2) * (f x - goL f x)) = 0) :
    ∃ v F : ℝ → ℝ, (∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt v (F x / (1 - x ^ 2) ^ 2) x) ∧
      (∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt F ((1 - x ^ 2) * v x) x) ∧
      ∀ᵐ x ∂(volume.restrict (Ioo (-1:ℝ) 1)), u x = v x := by
  have hu := locInt_of_L2 hint hmeas
  -- Step 2: remove the mean-zero condition
  obtain ⟨c, hc⟩ := kernel_trick (locInt_wm hu) (locInt_wg hu) (weak_step1 hu hweak)
  -- Step 3: du Bois-Reymond
  set M : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, (wm u t - c) with hMdef
  have hmc : LocInt (fun t => wm u t - c) := (locInt_wm hu).sub (LocInt.const c)
  have hMc : ContinuousOn M (Ioo (-1:ℝ) 1) := hmc.continuousOn_primitive
  have hMloc : LocInt M := LocInt.of_continuousOn hMc
  obtain ⟨e, he⟩ := dbr1 ((locInt_wg hu).sub hMloc) (fun φ hφ => by
    have h1 : ∫ x in Ioo (-1:ℝ) 1, M x * deriv φ x =
        -∫ x in Ioo (-1:ℝ) 1, (wm u x - c) * φ x := ibp_I hmc hφ
    have h2 := hc φ hφ
    have iMφ := integrableOn_mul_test hMloc (deriv_mem_goA₀ hφ)
    have igφ := integrableOn_mul_test (locInt_wg hu) (deriv_mem_goA₀ hφ)
    have imφ := integrableOn_mul_test (locInt_wm hu) hφ
    have iφ := integrableOn_test hφ
    have e1 : ∀ x, (wg u x - M x) * deriv φ x = wg u x * deriv φ x - M x * deriv φ x :=
      fun x => by ring
    have e2 : ∀ x, (wm u x - c) * φ x = wm u x * φ x - c * φ x := fun x => by ring
    simp_rw [e1]
    simp_rw [e2] at h1
    rw [integral_sub igφ iMφ, h1, integral_sub imφ (iφ.const_mul c),
      MeasureTheory.integral_const_mul]
    rw [integral_add imφ igφ] at h2
    linarith)
  -- Step 4: continuity, then differentiability
  have hw : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) ^ 2 ≠ 0 := fun x hx => by
    have : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    positivity
  set v₀ : ℝ → ℝ := fun x => (M x + e) / (1 - x ^ 2) ^ 2 with hv₀
  have hae : ∀ᵐ x, x ∈ Ioo (-1:ℝ) 1 → u x = v₀ x := by
    filter_upwards [he] with x hx hxI
    have h1 := hx hxI
    simp only [wg] at h1
    have hwx := hw x hxI
    simp only [hv₀]
    rw [eq_div_iff hwx]
    linarith
  have hv₀c : ContinuousOn v₀ (Ioo (-1:ℝ) 1) :=
    (hMc.add continuousOn_const).div (by fun_prop) (fun x hx => hw x hx)
  have hkc : ContinuousOn (fun x => (1 - x ^ 2) * v₀ x) (Ioo (-1:ℝ) 1) :=
    (by fun_prop : Continuous fun x : ℝ => 1 - x ^ 2).continuousOn.mul hv₀c
  have haek : ∀ᵐ t, t ∈ Ioo (-1:ℝ) 1 → wk u t = (1 - t ^ 2) * v₀ t := by
    filter_upwards [hae] with t ht htI
    simp only [wk, ht htI]
  have hHd : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt (wH u) ((1 - x ^ 2) * v₀ x) x := fun x hx =>
    hasDerivAt_primitive_of_ae hkc haek hx
  have hHc : ContinuousOn (wH u) (Ioo (-1:ℝ) 1) := fun x hx =>
    (hHd x hx).continuousAt.continuousWithinAt
  have hmtc : ContinuousOn (fun x => wH u x - 4 * x * ((1 - x ^ 2) * v₀ x) - c) (Ioo (-1:ℝ) 1) :=
    (hHc.sub ((by fun_prop : Continuous fun x : ℝ => 4 * x).continuousOn.mul hkc)).sub
      continuousOn_const
  have haem : ∀ᵐ t, t ∈ Ioo (-1:ℝ) 1 →
      wm u t - c = wH u t - 4 * t * ((1 - t ^ 2) * v₀ t) - c := by
    filter_upwards [haek] with t ht htI
    simp only [wm, ht htI]
  have hMd : ∀ x ∈ Ioo (-1:ℝ) 1,
      HasDerivAt M (wH u x - 4 * x * ((1 - x ^ 2) * v₀ x) - c) x := fun x hx =>
    hasDerivAt_primitive_of_ae hmtc haem hx
  refine ⟨v₀, fun x => wH u x - c, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have hwx := hw x hx
    have hPd : HasDerivAt (fun x : ℝ => (1 - x ^ 2) ^ 2) (2 * (1 - x ^ 2) * (-(2 * x))) x := by
      have := (((hasDerivAt_pow 2 x).const_sub 1).pow 2)
      convert this using 1
      simp
    have hdiv := ((hMd x hx).add_const e).div hPd hwx
    have hw1 : 1 - x ^ 2 ≠ 0 := fun h => hwx (by rw [h]; ring)
    have hv : M x + e = (1 - x ^ 2) ^ 2 * v₀ x := by simp only [hv₀]; field_simp
    refine hdiv.congr_deriv ?_
    rw [hv]
    field_simp
    ring
  · exact (hHd x hx).sub_const c
  · exact (ae_restrict_iff' measurableSet_Ioo).2 hae

end MarkovTriple.BGL.Instances.GegenbauerOpen.ESA
