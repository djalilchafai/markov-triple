import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticWeakForm

/-!
# Scaled even mollifiers with the Friedrichs gradient bound (R16, Friedrichs step)

Statements K1, Y1 of `STATEMENTS_R16_Friedrichs.md`.  Textbook: Gilbarg–Trudinger §7.2 (mollifiers),
Friedrichs 1944 (the bound `∫ |∇ρ_ε(z)| |z| dz ≤ C` is scale invariant).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- **K1**: a mollifier sequence that is even and has `∫ |∂ᵢρ_n(z)| ‖z‖ dz ≤ C₁` uniformly in `n` and `i`. -/
structure IsFrMollSeq (ρ : ℕ → (Fin d → ℝ) → ℝ) : Prop where
  moll : IsMollSeq ρ
  even : ∀ n x, ρ n (-x) = ρ n x
  grad : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ n i, ∫ z, |pderiv (ρ n) i z| * ‖z‖ ≤ C₁

/-- chain rule for a dilation -/
lemma pderiv_comp_smul {s : (Fin d → ℝ) → ℝ} (hs : Sm s) (c : ℝ) (i : Fin d) (z : Fin d → ℝ) :
    pderiv (fun x => s (c • x)) i z = c * pderiv s i (c • z) := by
  have h1 : HasFDerivAt s (fderiv ℝ s (c • z)) (c • z) := (hs.differentiableAt _).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Fin d → ℝ => c • x) (c • ContinuousLinearMap.id ℝ (Fin d → ℝ)) z :=
    (hasFDerivAt_id z).const_smul c
  have := (h1.comp z h2).fderiv
  unfold pderiv
  have e : (fun x : Fin d → ℝ => s (c • x)) = s ∘ (fun x => c • x) := rfl
  rw [e, this]
  simp

lemma exists_frMollSeq (d : ℕ) : ∃ ρ : ℕ → (Fin d → ℝ) → ℝ, IsFrMollSeq ρ := by
  obtain ⟨ρ0, h1, h2, h3, h4, h5⟩ := exists_mollifier d
  set r := ρ0 0 with hr
  set s : (Fin d → ℝ) → ℝ := fun x => (r x + r (-x)) / 2 with hs
  have hneg : Sm (fun x : Fin d → ℝ => r (-x)) := (h1 0).comp contDiff_neg
  have s_sm : Sm s := ((h1 0).add hneg).div_const 2
  have s_cs : HasCompactSupport s := by
    have a1 : HasCompactSupport (fun x : Fin d → ℝ => r (-x)) := by
      have := (h2 0).comp_homeomorph (Homeomorph.neg (Fin d → ℝ))
      exact this
    refine ((h2 0).add a1).mono' (subset_closure.trans' fun x hx => ?_)
    intro h0; exact hx (by simp [hs, Pi.add_apply] at h0 ⊢; linarith)
  have s_nn : ∀ x, 0 ≤ s x := fun x => by
    have := h3 0 x; have := h3 0 (-x); simp only [hs, hr]; linarith
  have s_int : ∫ x, s x = 1 := by
    have i1 : Integrable r := (h1 0).continuous.integrable_of_hasCompactSupport (h2 0)
    have i2 : Integrable (fun x : Fin d → ℝ => r (-x)) := i1.comp_neg
    simp only [hs]
    rw [integral_div, integral_add i1 i2, integral_neg_eq_self (fun x => r x) volume]
    have := h4 0
    simp only [hr]; rw [this]; norm_num
  have s_supp : ∀ x, s x ≠ 0 → ‖x‖ < 1 := fun x hx => by
    by_contra hge
    push Not at hge
    have e1 : r x = 0 := by
      by_contra hne; have := h5 0 x hne; simp at this; linarith
    have e2 : r (-x) = 0 := by
      by_contra hne; have := h5 0 (-x) hne; simp at this; linarith
    exact hx (by simp only [hs, e1, e2]; norm_num)
  have s_even : ∀ x, s (-x) = s x := fun x => by simp only [hs, neg_neg]; ring
  -- scaled sequence
  set ρ : ℕ → (Fin d → ℝ) → ℝ := fun n x => (((n : ℝ) + 1) ^ d) * s (((n : ℝ) + 1) • x) with hρ
  have hc : ∀ n : ℕ, ((n : ℝ) + 1) ≠ 0 := fun n => by positivity
  have hcd : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1) ^ d := fun n => by positivity
  have hfin : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  have ρ_sm : ∀ n, Sm (ρ n) := fun n =>
    contDiff_const.mul (s_sm.comp (contDiff_id.const_smul _))
  refine ⟨ρ, ⟨⟨ρ_sm, fun n => ?_, fun n x => ?_, fun n => ?_, fun n x hx => ?_⟩, fun n x => ?_, ?_⟩⟩
  · exact (s_cs.comp_smul (hc n)).mul_left
  · exact mul_nonneg (hcd n).le (s_nn _)
  · have := Measure.integral_comp_smul (volume : Measure (Fin d → ℝ)) (fun x => s x) ((n : ℝ) + 1)
    simp only [hρ]
    rw [integral_const_mul]
    simp only [hfin] at this
    rw [this, s_int]
    simp only [smul_eq_mul, mul_one]
    rw [abs_of_pos (inv_pos.2 (hcd n))]
    field_simp
  · have : s (((n : ℝ) + 1) • x) ≠ 0 := fun h0 => hx (by simp only [hρ, h0, mul_zero])
    have := s_supp _ this
    rw [norm_smul, Real.norm_of_nonneg (by positivity)] at this
    rw [lt_div_iff₀ (by positivity)]
    linarith
  · simp only [hρ, ← s_even (((n : ℝ) + 1) • x)]
    simp
  · -- gradient bound
    set C₁ : ℝ := ∑ i : Fin d, ∫ z, |pderiv s i z| * ‖z‖ with hC₁
    have hnn : ∀ i, 0 ≤ ∫ z, |pderiv s i z| * ‖z‖ := fun i =>
      integral_nonneg fun z => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    refine ⟨C₁, Finset.sum_nonneg fun i _ => hnn i, fun n i => ?_⟩
    have hpd : ∀ z, pderiv (ρ n) i z = ((n : ℝ) + 1) ^ d * (((n : ℝ) + 1) * pderiv s i (((n : ℝ) + 1) • z)) := by
      intro z
      have e : ρ n = ((n : ℝ) + 1) ^ d • (fun x => s (((n : ℝ) + 1) • x)) := rfl
      have hsm : Sm (fun x : Fin d → ℝ => s (((n : ℝ) + 1) • x)) := s_sm.comp (contDiff_id.const_smul _)
      rw [e, pderiv_smul _ hsm, pderiv_comp_smul s_sm]
    have hint : ∀ z, |pderiv (ρ n) i z| * ‖z‖ =
        ((n : ℝ) + 1) ^ d * ((fun y : Fin d → ℝ => |pderiv s i y| * ‖y‖) (((n : ℝ) + 1) • z)) := by
      intro z
      rw [hpd]
      have hn : ‖((n : ℝ) + 1) • z‖ = ((n : ℝ) + 1) * ‖z‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      simp only [hn, abs_mul, abs_of_pos (hcd n), abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)]
      ring
    simp_rw [hint]
    rw [integral_const_mul]
    have := Measure.integral_comp_smul (volume : Measure (Fin d → ℝ))
      (fun y : Fin d → ℝ => |pderiv s i y| * ‖y‖) ((n : ℝ) + 1)
    simp only [hfin] at this
    rw [this, abs_of_pos (inv_pos.2 (hcd n))]
    simp only [smul_eq_mul]
    have e : ((n : ℝ) + 1) ^ d * (((n : ℝ) + 1) ^ d)⁻¹ = 1 := mul_inv_cancel₀ (hcd n).ne'
    calc ((n : ℝ) + 1) ^ d * ((((n : ℝ) + 1) ^ d)⁻¹ * ∫ y, |pderiv s i y| * ‖y‖)
        = ∫ y, |pderiv s i y| * ‖y‖ := by rw [← mul_assoc, e, one_mul]
      _ ≤ C₁ := Finset.single_le_sum (f := fun i => ∫ z, |pderiv s i z| * ‖z‖)
          (fun i _ => hnn i) (Finset.mem_univ i)

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
