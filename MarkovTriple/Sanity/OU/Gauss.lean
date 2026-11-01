import MarkovTriple.Sanity.OU.Basic

/-! # OU (Part 2): Gaussian density, integrability, integration by parts -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

instance : IsProbabilityMeasure γ := inferInstance

lemma φ_def (x : ℝ) : φ x = (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [gaussianPDFReal_def]

lemma φ_pos (x : ℝ) : 0 < φ x := gaussianPDFReal_pos 0 1 x one_ne_zero

lemma φ_hasDerivAt (x : ℝ) : HasDerivAt φ (-x * φ x) x := by
  have e : φ = fun x => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) := funext φ_def
  rw [e]
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert this using 1
    simp; ring
  have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
  convert h2 using 1
  simp only []; ring

lemma φ_contDiff : Sm φ := by
  have e : φ = fun x => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) := funext φ_def
  rw [e]
  exact contDiff_const.mul (Real.contDiff_exp.comp ((contDiff_id.pow 2).neg.div_const 2))

lemma integrable_γ_iff {F : ℝ → ℝ} : Integrable F γ ↔ Integrable (fun x => φ x * F x) := by
  show Integrable F (gaussianReal 0 1) ↔ _
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [toReal_gaussianPDF, smul_eq_mul]

lemma integral_γ {F : ℝ → ℝ} : ∫ x, F x ∂γ = ∫ x, φ x * F x := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp [smul_eq_mul]

/-- **Gaussian integration by parts**: `∫ g · L f dγ = −∫ g' f' dγ` whenever the three products
are `γ`-integrable (`g`, `f` smooth). -/
theorem ibp_master {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g)
    (h1 : Integrable (fun x => g x * Lo f x) γ)
    (h2 : Integrable (fun x => deriv g x * deriv f x) γ)
    (h3 : Integrable (fun x => g x * deriv f x) γ) :
    ∫ x, g x * Lo f x ∂γ = -∫ x, deriv g x * deriv f x ∂γ := by
  have hv : ∀ x, HasDerivAt (fun x => deriv f x * φ x) (Lo f x * φ x) x := by
    intro x
    have := ((hf.deriv'.hasDerivAt x).mul (φ_hasDerivAt x))
    convert this using 1
    unfold Lo; ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := fun x => deriv f x * φ x) (u' := deriv g) (v' := fun x => Lo f x * φ x)
    (fun x _ => hg.hasDerivAt x) (fun x _ => hv x)
    (by
      have := (integrable_γ_iff.1 h1)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      have := (integrable_γ_iff.1 h2)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      have := (integrable_γ_iff.1 h3)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
  rw [integral_γ, integral_γ (F := fun x => deriv g x * deriv f x)]
  have e1 : (fun x => φ x * (g x * Lo f x)) = fun x => g x * (Lo f x * φ x) := by
    funext x; ring
  have e2 : (fun x => φ x * (deriv g x * deriv f x)) = fun x => deriv g x * (deriv f x * φ x) := by
    funext x; ring
  rw [e1, e2]
  exact key

/-! ### Polynomial growth -/

/-- polynomial growth bound -/
def PG (F : ℝ → ℝ) : Prop :=
  Continuous F ∧ ∃ (C : ℝ) (N : ℕ), ∀ x, |F x| ≤ C * (1 + |x|) ^ N

lemma integrable_pow_abs (N : ℕ) : Integrable (fun x : ℝ => |x| ^ N) γ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have := (memLp_id_gaussianReal' (μ := 0) (v := 1) (N : ℝ≥0∞) (by simp)).integrable_norm_pow
      (by simpa using hN.ne')
    simpa using this

lemma one_add_abs_pow_le (N : ℕ) (x : ℝ) : (1 + |x|) ^ N ≤ 2 ^ N * (1 + |x| ^ N) := by
  have h0 : 0 ≤ |x| := abs_nonneg x
  rcases le_total |x| 1 with h | h
  · have : (1 + |x|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have h1 : 0 ≤ |x| ^ N := pow_nonneg h0 N
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) N]
  · have : (1 + |x|) ^ N ≤ (2 * |x|) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at this
    have h1 : 0 ≤ |x| ^ N := pow_nonneg h0 N
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) N]

lemma integrable_one_add_abs_pow (N : ℕ) : Integrable (fun x : ℝ => (1 + |x|) ^ N) γ := by
  refine Integrable.mono' (g := fun x => 2 ^ N * (1 + |x| ^ N))
    ((integrable_const _).add (integrable_pow_abs N) |>.const_mul _) ?_ ?_
  · exact ((continuous_const.add continuous_abs).pow N).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact one_add_abs_pow_le N x

lemma PG.integrable {F : ℝ → ℝ} (h : PG F) : Integrable F γ := by
  obtain ⟨hc, C, N, hb⟩ := h
  refine Integrable.mono' ((integrable_one_add_abs_pow N).const_mul C) hc.aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by simpa using hb x

lemma PG.mul {F G : ℝ → ℝ} (hF : PG F) (hG : PG G) : PG (fun x => F x * G x) := by
  obtain ⟨hc, C, N, hb⟩ := hF
  obtain ⟨hc', C', N', hb'⟩ := hG
  refine ⟨hc.mul hc', |C| * |C'|, N + N', fun x => ?_⟩
  rw [abs_mul, pow_add]
  have h1 := (hb x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h2 := (hb' x).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
  calc |F x| * |G x| ≤ (|C| * (1 + |x|) ^ N) * (|C'| * (1 + |x|) ^ N') :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = |C| * |C'| * ((1 + |x|) ^ N * (1 + |x|) ^ N') := by ring

lemma PG.add {F G : ℝ → ℝ} (hF : PG F) (hG : PG G) : PG (fun x => F x + G x) := by
  obtain ⟨hc, C, N, hb⟩ := hF
  obtain ⟨hc', C', N', hb'⟩ := hG
  refine ⟨hc.add hc', |C| + |C'|, max N N', fun x => ?_⟩
  have h1 : (1 + |x|) ^ N ≤ (1 + |x|) ^ max N N' :=
    pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_left _ _)
  have h2 : (1 + |x|) ^ N' ≤ (1 + |x|) ^ max N N' :=
    pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_right _ _)
  have e1 := (hb x).trans (mul_le_mul (le_abs_self C) h1 (by positivity) (abs_nonneg _))
  have e2 := (hb' x).trans (mul_le_mul (le_abs_self C') h2 (by positivity) (abs_nonneg _))
  calc |F x + G x| ≤ |F x| + |G x| := abs_add_le _ _
    _ ≤ _ := by nlinarith

lemma PG.const_mul {F : ℝ → ℝ} (c : ℝ) (hF : PG F) : PG (fun x => c * F x) := by
  obtain ⟨hc, C, N, hb⟩ := hF
  refine ⟨continuous_const.mul hc, |c| * C, N, fun x => ?_⟩
  rw [abs_mul]
  calc |c| * |F x| ≤ |c| * (C * (1 + |x|) ^ N) := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
    _ = _ := by ring

lemma PG.sub {F G : ℝ → ℝ} (hF : PG F) (hG : PG G) : PG (fun x => F x - G x) := by
  have := hF.add (hG.const_mul (-1))
  simpa [sub_eq_add_neg] using this

lemma pg_id : PG (fun x : ℝ => x) :=
  ⟨continuous_id, 1, 1, fun x => by simp⟩

lemma pg_const (c : ℝ) : PG (fun _ : ℝ => c) :=
  ⟨continuous_const, |c|, 0, fun x => by simp⟩

lemma PG.memLp_two {F : ℝ → ℝ} (h : PG F) : MemLp F 2 γ := by
  rw [memLp_two_iff_integrable_sq h.1.aestronglyMeasurable]
  have := (h.mul h).integrable
  simpa [sq] using this

lemma pg_bounded {F : ℝ → ℝ} (hc : Continuous F) (hb : ∃ C, ∀ x, |F x| ≤ C) : PG F := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨hc, C, 0, fun x => ?_⟩
  simpa using hC x

lemma PG.of_cs {F : ℝ → ℝ} (hc : Continuous F) (hs : HasCompactSupport F) : PG F :=
  pg_bounded hc (by
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
    exact ⟨C, fun x => by simpa using hC x⟩)

end MarkovTriple.Sanity.OU
