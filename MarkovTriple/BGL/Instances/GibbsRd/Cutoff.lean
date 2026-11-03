import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Calculus

/-!
# Smooth radial cut-offs on `ℝ^d` (for the exhaustion sequence of BGL Def. 3.1.1 and completeness, Def. 3.3.9)

`cut R x = s(2 − |x|²/R²)` with `s = Real.smoothTransition` and `|x|² = Σ xᵢ²`: smooth, `0 ≤ cut ≤ 1`, `= 1` on
`|x|² ≤ R²`, `= 0` on `|x|² ≥ 2R²`, compactly supported, increasing in `R`, and
`Σᵢ (∂ᵢ cut R)² ≤ 8 C²/R²` where `C` bounds `s'`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- `|x|² = Σ xᵢ²`. -/
noncomputable def qd (x : Rd d) : ℝ := ∑ i, x i ^ 2

lemma qd_nonneg (x : Rd d) : 0 ≤ qd x := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sm_qd : Sm (qd : Rd d → ℝ) :=
  ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i)).pow 2

lemma pderiv_coord (i j : Fin d) (x : Rd d) :
    pderiv (fun y : Rd d => y i) j x = if j = i then 1 else 0 := by
  have : HasFDerivAt (fun y : Rd d => y i) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x :=
    hasFDerivAt_apply i x
  unfold pderiv
  rw [this.fderiv]
  by_cases h : j = i <;> simp [h]

lemma pderiv_qd (j : Fin d) (x : Rd d) : pderiv qd j x = 2 * x j := by
  have h : ∀ i, pderiv (fun y : Rd d => y i ^ 2) j x = if j = i then 2 * x i else 0 := by
    intro i
    have hd : HasFDerivAt (fun y : Rd d => y i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := hasFDerivAt_apply i x
    have := hd.pow 2
    unfold pderiv
    rw [this.fderiv]
    by_cases hji : j = i <;> simp [hji]
  unfold qd
  rw [pderiv_sum _ (fun i => ((contDiff_apply ℝ ℝ i)).pow 2) j x]
  simp [h]

/-- the derivative of `s = smoothTransition` vanishes off `[0,1]`, and is bounded. -/
lemma sT_deriv_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) : deriv Real.smoothTransition y = 0 := by
  have hmin : IsLocalMin Real.smoothTransition y := by
    refine IsMinOn.isLocalMin (s := Set.univ) (fun z _ => ?_) Filter.univ_mem
    show Real.smoothTransition y ≤ Real.smoothTransition z
    rw [Real.smoothTransition.zero_of_nonpos hy]
    exact Real.smoothTransition.nonneg z
  exact hmin.deriv_eq_zero

lemma sT_deriv_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) : deriv Real.smoothTransition y = 0 := by
  have hmax : IsLocalMax Real.smoothTransition y := by
    refine IsMaxOn.isLocalMax (s := Set.univ) (fun z _ => ?_) Filter.univ_mem
    show Real.smoothTransition z ≤ Real.smoothTransition y
    rw [Real.smoothTransition.one_of_one_le hy]
    exact Real.smoothTransition.le_one z
  exact hmax.deriv_eq_zero

lemma sT_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |deriv Real.smoothTransition y| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.1 Real.smoothTransition.contDiff).2.continuous
  have hcs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun y hy => ?_
    rcases lt_or_ge y 0 with h | h
    · exact sT_deriv_zero_of_nonpos h.le
    · exact sT_deriv_zero_of_one_le (by
        by_contra h1
        exact hy ⟨h, (not_le.1 h1).le⟩)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨max C 0, le_max_right _ _, fun y => by
    have := hC y
    simp only [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

/-- the radial cut-off at scale `R` -/
noncomputable def cut (R : ℝ) (x : Rd d) : ℝ := Real.smoothTransition (2 - qd x / R ^ 2)

lemma sm_cut (R : ℝ) : Sm (cut R : Rd d → ℝ) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (sm_qd.div_const _))

lemma cut_nonneg (R : ℝ) (x : Rd d) : 0 ≤ cut R x := Real.smoothTransition.nonneg _

lemma cut_le_one (R : ℝ) (x : Rd d) : cut R x ≤ 1 := Real.smoothTransition.le_one _

lemma cut_eq_one {R : ℝ} (hR : 0 < R) {x : Rd d} (h : qd x ≤ R ^ 2) : cut R x = 1 := by
  unfold cut
  apply Real.smoothTransition.one_of_one_le
  have : qd x / R ^ 2 ≤ 1 := (div_le_one (by positivity)).2 h
  linarith

lemma cut_eq_zero {R : ℝ} (hR : 0 < R) {x : Rd d} (h : 2 * R ^ 2 ≤ qd x) : cut R x = 0 := by
  unfold cut
  apply Real.smoothTransition.zero_of_nonpos
  have : 2 ≤ qd x / R ^ 2 := (le_div_iff₀ (by positivity)).2 (by linarith)
  linarith

lemma hcs_cut {R : ℝ} (hR : 0 < R) : HasCompactSupport (cut R : Rd d → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) (2 * R)) fun x hx => ?_
  apply cut_eq_zero hR
  by_contra hlt
  push Not at hlt
  apply hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have h1 : x i ^ 2 ≤ qd x := by
    unfold qd
    exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : x i ^ 2 ≤ (2 * R) ^ 2 := by nlinarith
  have := abs_le_of_sq_le_sq' h2 (by positivity)
  exact this

lemma cut_mono {R R' : ℝ} (hR : 0 < R) (hRR : R ≤ R') (x : Rd d) : cut R x ≤ cut R' x := by
  unfold cut
  apply Real.smoothTransition.monotone
  have h1 : R ^ 2 ≤ R' ^ 2 := pow_le_pow_left₀ hR.le hRR 2
  have : qd x / R' ^ 2 ≤ qd x / R ^ 2 :=
    div_le_div_of_nonneg_left (qd_nonneg x) (by positivity) h1
  linarith

lemma pderiv_cut {R : ℝ} (j : Fin d) (x : Rd d) :
    pderiv (cut R) j x = deriv Real.smoothTransition (2 - qd x / R ^ 2) * (-(2 * x j / R ^ 2)) := by
  have hq : HasFDerivAt (qd : Rd d → ℝ) (fderiv ℝ qd x) x := (sm_qd.differentiableAt x).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Rd d => 2 - qd y / R ^ 2) (-((R ^ 2)⁻¹ • fderiv ℝ qd x)) x := by
    have := (hq.const_mul ((R ^ 2)⁻¹)).const_sub 2
    simpa [div_eq_inv_mul] using this
  have h3 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (2 - qd x / R ^ 2))
      (2 - qd x / R ^ 2) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt
  have h4 := h3.comp_hasFDerivAt x h2
  unfold pderiv cut
  rw [show (fun x : Rd d => Real.smoothTransition (2 - qd x / R ^ 2)) =
    Real.smoothTransition ∘ fun y : Rd d => 2 - qd y / R ^ 2 from rfl, h4.fderiv]
  have := pderiv_qd j x
  unfold pderiv at this
  show deriv Real.smoothTransition (2 - qd x / R ^ 2) *
    (-((R ^ 2)⁻¹ * (fderiv ℝ qd x) (Pi.single j 1))) = _
  rw [this]
  ring

lemma sum_sq_pderiv_cut_le {R C : ℝ} (hR : 0 < R) (hC : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    (x : Rd d) : ∑ j, pderiv (cut R) j x ^ 2 ≤ 8 * C ^ 2 / R ^ 2 := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  by_cases hq : qd x < 2 * R ^ 2
  · have hsum : ∑ j, pderiv (cut R) j x ^ 2 =
        deriv Real.smoothTransition (2 - qd x / R ^ 2) ^ 2 * (4 * qd x / R ^ 4) := by
      simp only [pderiv_cut, mul_pow, neg_sq, div_pow]
      rw [← Finset.mul_sum]
      congr 1
      unfold qd
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
      ring
    rw [hsum]
    have h1 : deriv Real.smoothTransition (2 - qd x / R ^ 2) ^ 2 ≤ C ^ 2 := by
      have := hC (2 - qd x / R ^ 2)
      nlinarith [abs_nonneg (deriv Real.smoothTransition (2 - qd x / R ^ 2)), sq_abs
        (deriv Real.smoothTransition (2 - qd x / R ^ 2))]
    have h2 : 4 * qd x / R ^ 4 ≤ 8 / R ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : R ^ 4 = R ^ 2 * R ^ 2 := by ring
      nlinarith [sq_nonneg R, qd_nonneg x]
    calc _ ≤ C ^ 2 * (8 / R ^ 2) :=
          mul_le_mul h1 h2 (div_nonneg (by nlinarith [qd_nonneg x]) (by positivity)) (by positivity)
      _ = 8 * C ^ 2 / R ^ 2 := by ring
  · push Not at hq
    have : deriv Real.smoothTransition (2 - qd x / R ^ 2) = 0 := by
      apply sT_deriv_zero_of_nonpos
      have : 2 ≤ qd x / R ^ 2 := (le_div_iff₀ (by positivity)).2 (by linarith)
      linarith
    simp only [pderiv_cut, this, zero_mul]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity

end MarkovTriple.BGL.Instances.GibbsRd
