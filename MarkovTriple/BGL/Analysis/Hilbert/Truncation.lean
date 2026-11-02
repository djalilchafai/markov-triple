import Mathlib
import MarkovTriple.BGL.Frozen.PartialDeriv

/-!
# Scalar smooth truncations (`ψ_δ(t) = √(t²+δ²) − δ`, smooth clip) and the closed set `{w ≤ 1}`

Ported (statements unchanged, `MarkovTriple.pderiv` replaced by the identical
`MarkovTriple.BGL.pderiv`) from the legacy `Hilbert/MarkovCriterion.lean` and `Hilbert/SubMarkov.lean`.
Used by `BGL/Semigroup/Markov.lean` (positivity and sub-Markov property of the Friedrichs semigroup).
-/

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

noncomputable def trunc (δ : ℝ) (z : Fin 1 → ℝ) : ℝ := √(z 0 ^ 2 + δ ^ 2) - δ

lemma contDiff_trunc {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ (⊤ : ℕ∞) (trunc δ) := by
  unfold trunc
  refine ContDiff.sub ?_ contDiff_const
  refine ContDiff.sqrt ?_ (fun z => by positivity)
  exact ((contDiff_apply ℝ ℝ 0).pow 2).add contDiff_const

lemma trunc_zero {δ : ℝ} (hδ : 0 < δ) : trunc δ 0 = 0 := by
  simp [trunc, Real.sqrt_sq hδ.le]

lemma pderiv_trunc {δ : ℝ} (hδ : 0 < δ) (z : Fin 1 → ℝ) :
    MarkovTriple.BGL.pderiv (trunc δ) 0 z = z 0 / √(z 0 ^ 2 + δ ^ 2) := by
  have hpos : 0 < z 0 ^ 2 + δ ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => √(t ^ 2 + δ ^ 2) - δ) (z 0 / √(z 0 ^ 2 + δ ^ 2)) (z 0) := by
    have := ((((hasDerivAt_id (z 0)).pow 2).add_const (δ ^ 2)).sqrt hpos.ne').sub_const δ
    refine this.congr_deriv ?_
    have : 0 < √(z 0 ^ 2 + δ ^ 2) := Real.sqrt_pos.2 hpos
    simp only [id, Pi.pow_apply]
    field_simp
    norm_num
  have h2 := h1.comp_hasFDerivAt z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  unfold MarkovTriple.BGL.pderiv
  have h3 : fderiv ℝ (trunc δ) z = _ := h2.fderiv
  rw [h3]
  simp

lemma abs_pderiv_trunc_le {δ : ℝ} (hδ : 0 < δ) (z : Fin 1 → ℝ) :
    |MarkovTriple.BGL.pderiv (trunc δ) 0 z| ≤ 1 := by
  rw [pderiv_trunc hδ, abs_div, abs_of_pos (Real.sqrt_pos.2 (by positivity : 0 < z 0 ^ 2 + δ ^ 2))]
  rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
  calc |z 0| = √(z 0 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])

lemma trunc_bounds {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ |t| - (√(t ^ 2 + δ ^ 2) - δ) ∧ |t| - (√(t ^ 2 + δ ^ 2) - δ) ≤ min δ |t| := by
  have h1 : |t| ≤ √(t ^ 2 + δ ^ 2) := by
    calc |t| = √(t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
  have h2 : √(t ^ 2 + δ ^ 2) ≤ |t| + δ := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_abs t, abs_nonneg t]
  have h3 : δ ≤ √(t ^ 2 + δ ^ 2) := by
    calc δ = √(δ ^ 2) := (Real.sqrt_sq hδ.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  refine ⟨by linarith, le_min (by linarith) (by linarith)⟩



lemma abs_min_le (a c : ℝ) (hc : 0 ≤ c) : |min a c| ≤ |a| := by
  rcases le_total a c with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_of_nonneg hc]; exact h.trans (le_abs_self a)

/-- Smooth approximation of `t ↦ t ∧ c`. -/
noncomputable def clipFn (c δ : ℝ) (z : Fin 1 → ℝ) : ℝ :=
  (z 0 - √((z 0 - c) ^ 2 + δ ^ 2) + √(c ^ 2 + δ ^ 2)) / 2

lemma contDiff_clipFn {δ : ℝ} (hδ : 0 < δ) (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (clipFn c δ) := by
  unfold clipFn
  refine ContDiff.div_const (ContDiff.add (ContDiff.sub (contDiff_apply ℝ ℝ 0) ?_)
    contDiff_const) 2
  refine ContDiff.sqrt ?_ (fun z => by positivity)
  exact (((contDiff_apply ℝ ℝ 0).sub contDiff_const).pow 2).add contDiff_const

lemma clipFn_zero (c δ : ℝ) : clipFn c δ 0 = 0 := by
  simp [clipFn]

lemma pderiv_clipFn {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (z : Fin 1 → ℝ) :
    MarkovTriple.BGL.pderiv (clipFn c δ) 0 z =
      (1 - (z 0 - c) / √((z 0 - c) ^ 2 + δ ^ 2)) / 2 := by
  have hpos : 0 < (z 0 - c) ^ 2 + δ ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (t - √((t - c) ^ 2 + δ ^ 2) + √(c ^ 2 + δ ^ 2)) / 2)
      ((1 - (z 0 - c) / √((z 0 - c) ^ 2 + δ ^ 2)) / 2) (z 0) := by
    have h := ((((hasDerivAt_id (z 0)).sub_const c).pow 2).add_const (δ ^ 2)).sqrt hpos.ne'
    have h' := (((hasDerivAt_id (z 0)).sub h).add_const (√(c ^ 2 + δ ^ 2))).div_const 2
    refine h'.congr_deriv ?_
    have : 0 < √((z 0 - c) ^ 2 + δ ^ 2) := Real.sqrt_pos.2 hpos
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  have h2 := h1.comp_hasFDerivAt z
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  unfold MarkovTriple.BGL.pderiv
  have h3 : fderiv ℝ (clipFn c δ) z = _ := h2.fderiv
  rw [h3]
  simp

lemma abs_pderiv_clipFn_le {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (z : Fin 1 → ℝ) :
    |MarkovTriple.BGL.pderiv (clipFn c δ) 0 z| ≤ 1 := by
  rw [pderiv_clipFn hδ]
  have hApos : 0 < √((z 0 - c) ^ 2 + δ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hr : |(z 0 - c) / √((z 0 - c) ^ 2 + δ ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hApos, div_le_one hApos]
    calc |z 0 - c| = √((z 0 - c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
  obtain ⟨h1, h2⟩ := abs_le.1 hr
  rw [abs_le]
  constructor <;> linarith

lemma abs_sqrt_sub_sqrt_le (x y δ : ℝ) :
    |√(x ^ 2 + δ ^ 2) - √(y ^ 2 + δ ^ 2)| ≤ |x - y| := by
  set X := √(x ^ 2 + δ ^ 2) with hX
  set Y := √(y ^ 2 + δ ^ 2) with hY
  have hX2 : X ^ 2 = x ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  have hY2 : Y ^ 2 = y ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hXY : δ ^ 2 + x * y ≤ X * Y := by
    by_cases h : δ ^ 2 + x * y ≤ 0
    · exact h.trans (mul_nonneg hX0 hY0)
    · push Not at h
      apply le_of_sq_le_sq _ (mul_nonneg hX0 hY0)
      · rw [mul_pow, hX2, hY2]; nlinarith [sq_nonneg (δ * (x - y))]
  apply sq_le_sq.1
  nlinarith

lemma clipFn_bounds {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    |clipFn c δ (fun _ => t)| ≤ |t| ∧ |clipFn c δ (fun _ => t) - min t c| ≤ δ := by
  have hpos : 0 ≤ (t - c) ^ 2 + δ ^ 2 := by positivity
  set A := √((t - c) ^ 2 + δ ^ 2) with hA
  set B := √(c ^ 2 + δ ^ 2) with hB
  have hAB : |A - B| ≤ |t| := by
    have := abs_sqrt_sub_sqrt_le (t - c) (-c) δ
    rw [neg_sq] at this
    simpa [hA, hB] using this
  have hA1' : |t - c| ≤ A := by
    have := (trunc_bounds hδ (t - c)).2; have := min_le_left δ |t - c|; linarith
  have hA2' : A ≤ |t - c| + δ := by
    have := (trunc_bounds hδ (t - c)).1; linarith
  have hB1' : c ≤ B := by
    have := (trunc_bounds hδ c).2; have := min_le_left δ |c|
    rw [abs_of_nonneg hc] at *; linarith
  have hB2' : B ≤ c + δ := by
    have := (trunc_bounds hδ c).1; rw [abs_of_nonneg hc] at *; linarith
  have hd : clipFn c δ (fun _ => t) = (t - A + B) / 2 := rfl
  rw [hd]
  obtain ⟨h1, h2⟩ := abs_le.1 hAB
  constructor
  · rw [abs_le]
    constructor <;> nlinarith [neg_abs_le t, le_abs_self t]
  · rcases le_total t c with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith : t - c ≤ 0)] at *
      rw [abs_le]; constructor <;> linarith
    · rw [min_eq_right h, abs_of_nonneg (by linarith : 0 ≤ t - c)] at *
      rw [abs_le]; constructor <;> linarith

variable {E : Type*} [MeasurableSpace E]

lemma isClosed_ae_le_one (μ : Measure E) :
    IsClosed {w : Lp ℝ 2 μ | (w : E → ℝ) ≤ᵐ[μ] (1 : E → ℝ)} := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨s, hs, hsw⟩ := mem_closure_iff_seq_limit.1 hw
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hsw).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, (s n : E → ℝ) x ≤ 1 := ae_all_iff.2 fun n => hs n
  filter_upwards [hae, hall] with x h1 h2
  exact le_of_tendsto' h1 (fun i => h2 (ns i))

end MarkovTriple.Hilbert
