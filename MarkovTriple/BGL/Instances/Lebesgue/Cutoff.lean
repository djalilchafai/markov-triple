import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Basic

/-!
# Cutoff approximation in `L²(ℝ)` (BGL §3.2: the completeness / ESA cutoff argument, 1-D)

If `u` is smooth with `u, u', u'' ∈ L²`, then the compactly supported smooth functions
`χ(x/(n+1)) u(x)` converge to `u` in `L²`, and their second derivatives converge to `u''` in `L²`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

/-- `‖[g]‖² = ∫ g²`. -/
lemma norm_toLp_sq {g : ℝ → ℝ} (hg : MemLp g 2 volume) : ‖hg.toLp g‖ ^ 2 = ∫ x, (g x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]
  simp [sq]

lemma tendsto_toLp_of_integral_sq {G : ℕ → ℝ → ℝ} {F : ℝ → ℝ} (hG : ∀ n, MemLp (G n) 2 volume)
    (hF : MemLp F 2 volume)
    (h : Tendsto (fun n => ∫ x, (G n x - F x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 (hF.toLp F)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ n, ‖(hG n).toLp (G n) - hF.toLp F‖ = Real.sqrt (∫ x, (G n x - F x) ^ 2) := by
    intro n
    have hd : MemLp (fun x => G n x - F x) 2 volume := (hG n).sub hF
    have h1 : (hG n).toLp (G n) - hF.toLp F = hd.toLp (fun x => G n x - F x) := by
      rw [← MemLp.toLp_sub]; rfl
    rw [h1, ← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq hd]
  simp only [e]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  exact this

/-- `m` bounded measurable, `w ∈ L²`. -/
lemma sq_mul_integrable {m w : ℝ → ℝ} (hm : Measurable m) {c : ℝ} (hc : ∀ x, |m x| ≤ c)
    (hw : MemLp w 2 volume) : Integrable (fun x => (m x * w x) ^ 2) ∧
      ∫ x, (m x * w x) ^ 2 ≤ c ^ 2 * ∫ x, (w x) ^ 2 := by
  have hw2 : Integrable (fun x => (w x) ^ 2) := hw.integrable_sq
  have hle : ∀ x, (m x * w x) ^ 2 ≤ c ^ 2 * (w x) ^ 2 := by
    intro x
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hc x, abs_nonneg (m x), sq_abs (m x)])
      (sq_nonneg _)
  have hint : Integrable (fun x => (m x * w x) ^ 2) := by
    refine Integrable.mono' (hw2.const_mul (c ^ 2)) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hm.aestronglyMeasurable.mul hw.aestronglyMeasurable).pow 2)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle x
  exact ⟨hint, by
    calc ∫ x, (m x * w x) ^ 2 ≤ ∫ x, c ^ 2 * (w x) ^ 2 :=
          integral_mono hint (hw2.const_mul _) hle
      _ = c ^ 2 * ∫ x, (w x) ^ 2 := integral_const_mul _ _⟩

lemma chi_deriv_bound : ∃ C, 0 ≤ C ∧ ∀ x, |deriv chi x| ≤ C := by
  obtain ⟨C, hC⟩ := chi_smooth.deriv'.continuous.bounded_above_of_compact_support chi_cs.deriv
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    simp only [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

lemma chi_deriv2_bound : ∃ C, 0 ≤ C ∧ ∀ x, |deriv (deriv chi) x| ≤ C := by
  obtain ⟨C, hC⟩ := chi_smooth.deriv'.deriv'.continuous.bounded_above_of_compact_support
    chi_cs.deriv.deriv
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    simp only [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

/-- the scale `R n = n + 1`. -/
noncomputable def Rn (n : ℕ) : ℝ := (n : ℝ) + 1

lemma Rn_pos (n : ℕ) : 0 < Rn n := by unfold Rn; positivity

lemma chiR_eq_one_of {R x : ℝ} (hR : 0 < R) (h : |x| ≤ R) : chiR R x = 1 := by
  unfold chiR
  apply chi_eq_one
  rw [abs_div, abs_of_pos hR, div_le_one hR]
  exact h

lemma abs_chiR_sub_one_le (R x : ℝ) : |chiR R x - 1| ≤ 1 := by
  have h1 := chi_nonneg (x / R)
  have h2 := chi_le_one (x / R)
  rw [abs_le]; unfold chiR; constructor <;> linarith

lemma tendsto_integral_sq_cut {w : ℝ → ℝ} (hw : MemLp w 2 volume) :
    Tendsto (fun n : ℕ => ∫ x, ((chiR (Rn n) x - 1) * w x) ^ 2) atTop (𝓝 0) := by
  have hw2 : Integrable (fun x => (w x) ^ 2) := hw.integrable_sq
  have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure ℝ))
    (F := fun (n : ℕ) x => ((chiR (Rn n) x - 1) * w x) ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => (w x) ^ 2)
    (fun n => ((((chiR_smooth _).continuous.sub continuous_const).aestronglyMeasurable).mul
      hw.aestronglyMeasurable).pow 2)
    hw2
    (fun n => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (by
        have := abs_chiR_sub_one_le (Rn n) x
        nlinarith [sq_abs (chiR (Rn n) x - 1), abs_nonneg (chiR (Rn n) x - 1)]))
    (Filter.Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with n hn
      have h1 : |x| ≤ Rn n := by
        unfold Rn
        have := (Nat.le_ceil |x|).trans (by exact_mod_cast hn : (⌈|x|⌉₊ : ℝ) ≤ n)
        linarith
      rw [chiR_eq_one_of (Rn_pos n) h1]; simp)
  simpa using this

theorem cutoff_tendsto {u : ℝ → ℝ} (hu : Sm u) (h0 : MemLp u 2 volume)
    (h1 : MemLp (deriv u) 2 volume) (h2 : MemLp (deriv (deriv u)) 2 volume)
    (hm : ∀ n : ℕ, MemLp (chiR (Rn n) * u) 2 volume)
    (hm2 : ∀ n : ℕ, MemLp (Lf (chiR (Rn n) * u)) 2 volume) :
    Tendsto (fun n : ℕ => (hm n).toLp (chiR (Rn n) * u)) atTop (𝓝 (h0.toLp u)) ∧
      Tendsto (fun n : ℕ => (hm2 n).toLp (Lf (chiR (Rn n) * u))) atTop
        (𝓝 (h2.toLp (deriv (deriv u)))) := by
  constructor
  · refine tendsto_toLp_of_integral_sq hm h0 ?_
    have := tendsto_integral_sq_cut h0
    refine this.congr (fun n => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  · refine tendsto_toLp_of_integral_sq hm2 h2 ?_
    obtain ⟨C1, hC1, hC1'⟩ := chi_deriv_bound
    obtain ⟨C2, hC2, hC2'⟩ := chi_deriv2_bound
    have hA := tendsto_integral_sq_cut h2
    have hu1 : Integrable (fun x => (deriv u x) ^ 2) := h1.integrable_sq
    have hu0 : Integrable (fun x => (u x) ^ 2) := h0.integrable_sq
    -- pointwise decomposition
    have hdec : ∀ n x, Lf (chiR (Rn n) * u) x - deriv (deriv u) x =
        (chiR (Rn n) x - 1) * deriv (deriv u) x + (2 * deriv (chiR (Rn n)) x) * deriv u x +
          deriv (deriv (chiR (Rn n))) x * u x := by
      intro n x
      rw [Lf_mul (chiR_smooth _) hu x]
      simp only [Lf]
      ring
    -- bounds on the cutoff derivatives
    have hb1 : ∀ n x, |2 * deriv (chiR (Rn n)) x| ≤ 2 * C1 / Rn n := by
      intro n x
      rw [deriv_chiR, abs_mul, abs_div, abs_of_pos (Rn_pos n)]
      rw [show (2 : ℝ) * C1 / Rn n = 2 * (C1 / Rn n) by ring]
      have := hC1' (x / Rn n)
      rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right this (Rn_pos n).le) (by norm_num)
    have hb2 : ∀ n x, |deriv (deriv (chiR (Rn n))) x| ≤ C2 / Rn n ^ 2 := by
      intro n x
      rw [deriv_deriv_chiR, abs_div, abs_of_pos (pow_pos (Rn_pos n) 2)]
      exact div_le_div_of_nonneg_right (hC2' _) (pow_pos (Rn_pos n) 2).le
    have hmB : ∀ n, Measurable (fun x => 2 * deriv (chiR (Rn n)) x) := fun n =>
      (((chiR_smooth _).deriv'.continuous).const_smul (2:ℝ)).measurable
    have hmC : ∀ n, Measurable (fun x => deriv (deriv (chiR (Rn n))) x) := fun n =>
      (chiR_smooth _).deriv'.deriv'.continuous.measurable
    have hmA : ∀ n, Measurable (fun x => chiR (Rn n) x - 1) := fun n =>
      ((chiR_smooth _).continuous.sub continuous_const).measurable
    have hAint : ∀ n, Integrable (fun x => ((chiR (Rn n) x - 1) * deriv (deriv u) x) ^ 2) :=
      fun n => (sq_mul_integrable (hmA n) (abs_chiR_sub_one_le _) h2).1
    -- the bound
    set bnd : ℕ → ℝ := fun n => 3 * ((∫ x, ((chiR (Rn n) x - 1) * deriv (deriv u) x) ^ 2) +
        (2 * C1 / Rn n) ^ 2 * (∫ x, (deriv u x) ^ 2) + (C2 / Rn n ^ 2) ^ 2 * (∫ x, (u x) ^ 2))
      with hbnd
    have hbnd0 : Tendsto bnd atTop (𝓝 0) := by
      have hr : Tendsto (fun n : ℕ => (1 : ℝ) / Rn n) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa [Rn] using this
      have hr2 : Tendsto (fun n : ℕ => (2 * C1 / Rn n) ^ 2) atTop (𝓝 0) := by
        have h := (hr.const_mul (2 * C1)).pow 2
        rw [mul_zero, zero_pow two_ne_zero] at h
        exact h.congr (fun n => by rw [mul_one_div])
      have hr3 : Tendsto (fun n : ℕ => (C2 / Rn n ^ 2) ^ 2) atTop (𝓝 0) := by
        have h := ((hr.pow 2).const_mul C2).pow 2
        rw [zero_pow two_ne_zero, mul_zero, zero_pow two_ne_zero] at h
        exact h.congr (fun n => by rw [one_div, inv_pow, ← div_eq_mul_inv])
      have := (hA.add (hr2.mul_const (∫ x, (deriv u x) ^ 2))).add (hr3.mul_const (∫ x, (u x) ^ 2))
      have h3 := this.const_mul 3
      simp only [zero_mul, add_zero, mul_zero] at h3
      exact h3
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hbnd0
    have hBint := (sq_mul_integrable (hmB n) (hb1 n) h1)
    have hCint := (sq_mul_integrable (hmC n) (hb2 n) h0)
    have hsum : Integrable (fun x => 3 * (((chiR (Rn n) x - 1) * deriv (deriv u) x) ^ 2 +
        ((2 * deriv (chiR (Rn n)) x) * deriv u x) ^ 2 +
        (deriv (deriv (chiR (Rn n))) x * u x) ^ 2)) :=
      ((hAint n).add hBint.1 |>.add hCint.1).const_mul 3
    calc ∫ x, (Lf (chiR (Rn n) * u) x - deriv (deriv u) x) ^ 2
        ≤ ∫ x, 3 * (((chiR (Rn n) x - 1) * deriv (deriv u) x) ^ 2 +
        ((2 * deriv (chiR (Rn n)) x) * deriv u x) ^ 2 +
        (deriv (deriv (chiR (Rn n))) x * u x) ^ 2) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hsum
            (Filter.Eventually.of_forall fun x => ?_)
          beta_reduce
          rw [hdec n x]
          nlinarith [sq_nonneg ((chiR (Rn n) x - 1) * deriv (deriv u) x -
            (2 * deriv (chiR (Rn n)) x) * deriv u x),
            sq_nonneg ((chiR (Rn n) x - 1) * deriv (deriv u) x -
            deriv (deriv (chiR (Rn n))) x * u x),
            sq_nonneg ((2 * deriv (chiR (Rn n)) x) * deriv u x -
            deriv (deriv (chiR (Rn n))) x * u x)]
      _ = 3 * ((∫ x, ((chiR (Rn n) x - 1) * deriv (deriv u) x) ^ 2) +
          (∫ x, ((2 * deriv (chiR (Rn n)) x) * deriv u x) ^ 2) +
          (∫ x, (deriv (deriv (chiR (Rn n))) x * u x) ^ 2)) := by
          have hAB : Integrable (fun x => ((chiR (Rn n) x - 1) * deriv (deriv u) x) ^ 2 +
              ((2 * deriv (chiR (Rn n)) x) * deriv u x) ^ 2) := (hAint n).add hBint.1
          rw [integral_const_mul, integral_add hAB hCint.1, integral_add (hAint n) hBint.1]
      _ ≤ bnd n := by
          rw [hbnd]
          have := hBint.2
          have := hCint.2
          linarith

end MarkovTriple.BGL.Lebesgue
