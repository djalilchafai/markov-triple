import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDerivAux1

/-!
# Taylor remainder and support estimates for the heat flow derivative on `ℝ^d` (Round 24, stream A, part H-b)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

lemma taylor1 {u u' u'' : ℝ → ℝ} {K : ℝ} (hu : ∀ t, HasDerivAt u (u' t) t)
    (hu' : ∀ t, HasDerivAt u' (u'' t) t) (hK : ∀ t, |u'' t| ≤ K) :
    |u 1 - u 0 - u' 0| ≤ K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hlip : ∀ τ, |u' τ - u' 0| ≤ K * |τ| := fun τ => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := u') (f' := u'') (C := K)
      (s := Set.univ) (x := 0) (y := τ) (fun x _ => (hu' x).hasDerivWithinAt)
      (fun x _ => by simpa using hK x) convex_univ trivial trivial
    simpa using this
  have hG : ∀ τ, HasDerivAt (fun s => u s - u 0 - s * u' 0) (u' τ - u' 0) τ := fun τ => by
    have := ((hu τ).sub_const (u 0)).sub ((hasDerivAt_id τ).mul_const (u' 0))
    have h3 : HasDerivAt ((fun x => u x - u 0) - fun y => y * u' 0) (u' τ - u' 0) τ := by
      simpa using this
    exact h3
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => u s - u 0 - s * u' 0)
    (f' := fun τ => u' τ - u' 0) (C := K) (s := Set.Icc (0 : ℝ) 1) (x := 0) (y := 1)
    (fun x _ => (hG x).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      refine (hlip x).trans ?_
      have : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      nlinarith)
    (convex_Icc 0 1) (by simp) (by simp)
  simpa using this

lemma hasDerivAt_line (y s : Fin d → ℝ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => y - τ • s) (-s) τ := by
  simpa using ((hasDerivAt_id τ).smul_const s).const_sub y

/-- Taylor remainder of order two with the operator norm of the second derivative. -/
lemma taylor_d {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) {C₂ : ℝ}
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C₂) (y s : Fin d → ℝ) :
    |φ (y - s) - φ y + fderiv ℝ φ y s| ≤ C₂ * ‖s‖ ^ 2 := by
  have hφ' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  have h1 : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => φ (y - τ • s)) (-(fderiv ℝ φ (y - τ • s) s)) τ :=
    fun τ => by
    have := ((hasFDerivAt_of hφ (y - τ • s))).comp_hasDerivAt τ (hasDerivAt_line y s τ)
    convert this using 1
    · rfl
    · simp
  have h2 : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => -(fderiv ℝ φ (y - τ • s) s))
      (fderiv ℝ (fderiv ℝ φ) (y - τ • s) s s) τ := fun τ => by
    have := (((hφ'.differentiable (by simp)) (y - τ • s)).hasFDerivAt).comp_hasDerivAt τ (hasDerivAt_line y s τ)
    have h3 := (this.clm_apply (hasDerivAt_const τ s)).neg
    convert h3 using 1
    · rfl
    · simp
  have := taylor1 h1 h2 (K := C₂ * ‖s‖ ^ 2) (fun τ => by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    have := hC₂ (y - τ • s)
    nlinarith [norm_nonneg s, mul_le_mul_of_nonneg_right this (mul_nonneg (norm_nonneg s) (norm_nonneg s))])
  simpa [sub_eq_add_neg] using this


/-- the integrand of the remainder of the difference quotient. -/
noncomputable def rhoD (φ : (Fin d → ℝ) → ℝ) (a h : ℝ) (x z : Fin d → ℝ) : ℝ :=
  (φ (x - (a + h) • z) - φ (x - a • z)) / h + fderiv ℝ φ (x - a • z) z

lemma rhoD_bound {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) {C₂ : ℝ}
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C₂) (a : ℝ) {h : ℝ} (hh : h ≠ 0) (x z : Fin d → ℝ) :
    |rhoD φ a h x z| ≤ C₂ * |h| * ‖z‖ ^ 2 := by
  have := taylor_d hφ hC₂ (x - a • z) (h • z)
  have e : rhoD φ a h x z =
      (φ (x - a • z - h • z) - φ (x - a • z) + fderiv ℝ φ (x - a • z) (h • z)) / h := by
    unfold rhoD
    have : x - (a + h) • z = x - a • z - h • z := by rw [add_smul]; abel
    rw [this, map_smul, smul_eq_mul]
    field_simp
  rw [e, abs_div, div_le_iff₀ (abs_pos.2 hh)]
  calc _ ≤ C₂ * ‖h • z‖ ^ 2 := this
    _ = C₂ * |h| * ‖z‖ ^ 2 * |h| := by
      rw [norm_smul, Real.norm_eq_abs]; ring

lemma exists_support {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < ‖y‖ → φ y = 0 ∧ fderiv ℝ φ y = 0 := by
  obtain ⟨R, hR⟩ := (cs hφ).isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩
  have hy' : y ∉ tsupport φ := fun hmem => by
    have := hR hmem
    rw [mem_closedBall_zero_iff] at this
    exact absurd (lt_of_le_of_lt (le_max_left _ _) hy) (not_lt.2 this)
  exact ⟨image_eq_zero_of_notMem_tsupport hy',
    image_eq_zero_of_notMem_tsupport (fun h => hy' (tsupport_fderiv_subset ℝ h))⟩

lemma rhoD_eq_zero {φ : (Fin d → ℝ) → ℝ} (a : ℝ) {R : ℝ}
    (hR : ∀ y, R < ‖y‖ → φ y = 0 ∧ fderiv ℝ φ y = 0)
    {h : ℝ} (hh : |h| ≤ 1) {x z : Fin d → ℝ} (hx : R + (|a| + 1) * ‖z‖ < ‖x‖) :
    rhoD φ a h x z = 0 := by
  have h1 : R < ‖x - (a + h) • z‖ := by
    have := norm_sub_norm_le x ((a + h) • z)
    have h2 : ‖(a + h) • z‖ ≤ (|a| + 1) * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc |a + h| ≤ |a| + |h| := abs_add_le _ _
        _ ≤ |a| + 1 := by linarith
    linarith
  have h3 : R < ‖x - a • z‖ := by
    have := norm_sub_norm_le x (a • z)
    have h2 : ‖a • z‖ ≤ (|a| + 1) * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    linarith
  unfold rhoD
  rw [(hR _ h1).1, (hR _ h3).1, (hR _ h3).2]
  simp

/-- the `z`-dependent bound for `∫ₓ |ρ|` (up to the factor `|h|`). -/
noncomputable def Wd (C₂ R a : ℝ) (z : Fin d → ℝ) : ℝ :=
  C₂ * ‖z‖ ^ 2 * (2 * (R + (|a| + 1) * ‖z‖)) ^ d

lemma integral_abs_rhoD_le {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) {C₂ : ℝ}
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C₂) (a : ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, R < ‖y‖ → φ y = 0 ∧ fderiv ℝ φ y = 0)
    {h : ℝ} (hh0 : h ≠ 0) (hh : |h| ≤ 1) (z : Fin d → ℝ) :
    ∫ x, |rhoD φ a h x z| ≤ |h| * Wd C₂ R a z := by
  set L := R + (|a| + 1) * ‖z‖ with hL
  have hL0 : 0 ≤ L := by positivity
  have hz0 : ∀ x ∉ Metric.closedBall (0 : Fin d → ℝ) L, |rhoD φ a h x z| = 0 := fun x hx => by
    rw [rhoD_eq_zero a hR hh ?_, abs_zero]
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz0]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Metric.closedBall (0 : Fin d → ℝ) L)
    (C := C₂ * |h| * ‖z‖ ^ 2) (f := fun x => |rhoD φ a h x z|) measure_closedBall_lt_top
    (fun x _ => by simpa using rhoD_bound hφ hC₂ a hh0 x z)
  rw [Real.norm_eq_abs, Measure.real, Real.volume_pi_closedBall _ hL0, ENNReal.toReal_ofReal
    (by positivity), Fintype.card_fin] at this
  refine (le_trans (le_abs_self _) this).trans (le_of_eq ?_)
  simp only [Wd, hL]
  ring

end MarkovTriple.BGL.LebesgueRd
