import Mathlib
import MarkovTriple.BGL.Instances.Circle.Modes

/-!
# F2 (positivity detection) on the circle (not frozen)

For continuous `f` in `𝒜₀ = C^∞(𝕋)`: if `∫ h f ≥ 0` for all nonnegative `h ∈ 𝒜₀` then `f ≥ 0` a.e.
Proof: `h = b²` with `b` a trigonometric polynomial uniformly close to `√(f⁻)` (Stone–Weierstrass,
`AC_top`), so `∫ (f⁻)² = −∫ f⁻ f` is bounded by every `ε > 0`.
-/

namespace MarkovTriple.BGL.Circle
open MeasureTheory AddCircle Filter Topology
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.Circle
local notation "𝒜c" => MarkovTriple.Sanity.Circle.A₀

lemma ae_nonneg_of_pairing {f : 𝕋 → ℝ} (hf : f ∈ 𝒜c)
    (h : ∀ g ∈ 𝒜c, 0 ≤ᵐ[μ₀] g → 0 ≤ ∫ x, g x * f x ∂μ₀) : 0 ≤ᵐ[μ₀] f := by
  have hfc : Continuous f := continuous_of_A₀ hf
  set m : 𝕋 → ℝ := fun x => max (-f x) 0 with hm
  have hmc : Continuous m := (hfc.neg).max continuous_const
  have hm0 : ∀ x, 0 ≤ m x := fun x => le_max_right _ _
  have hmf : ∀ x, m x * f x = -(m x) ^ 2 := by
    intro x
    simp only [hm]
    rcases le_total (-f x) 0 with h1 | h1
    · rw [max_eq_right h1]; nlinarith
    · rw [max_eq_left h1]; ring
  set s : 𝕋 → ℝ := fun x => Real.sqrt (m x) with hs
  have hsc : Continuous s := hmc.sqrt
  have hs2 : ∀ x, s x ^ 2 = m x := fun x => Real.sq_sqrt (hm0 x)
  obtain ⟨C1, hC1⟩ := bound_of_continuous hsc
  obtain ⟨K1, hK1⟩ := bound_of_continuous hfc
  set M : ℝ := |C1| with hM
  set K : ℝ := |K1| with hK
  have hM0 : 0 ≤ M := abs_nonneg _
  have hK0 : 0 ≤ K := abs_nonneg _
  have hsM : ∀ x, |s x| ≤ M := fun x => by
    have := hC1 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  have hfK : ∀ x, |f x| ≤ K := fun x => by
    have := hK1 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  have key : ∀ ε : ℝ, 0 < ε → ∫ x, (m x) ^ 2 ∂μ₀ ≤ ε := by
    intro ε hε
    have hden : 0 < (2 * M + 1) * (K + 1) := by positivity
    set δ : ℝ := min 1 (ε / ((2 * M + 1) * (K + 1))) with hδ
    have hδpos : 0 < δ := lt_min one_pos (div_pos hε hden)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ * ((2 * M + 1) * (K + 1)) ≤ ε := by
      have := min_le_right 1 (ε / ((2 * M + 1) * (K + 1)))
      calc δ * ((2 * M + 1) * (K + 1)) ≤ (ε / ((2 * M + 1) * (K + 1))) * ((2 * M + 1) * (K + 1)) :=
            mul_le_mul_of_nonneg_right this hden.le
        _ = ε := div_mul_cancel₀ _ hden.ne'
    let s' : C(𝕋, ℝ) := ⟨s, hsc⟩
    have hmem : s' ∈ closure (AC : Set C(𝕋, ℝ)) := by
      rw [← Subalgebra.topologicalClosure_coe, AC_top]; trivial
    obtain ⟨b, hbAC, hb⟩ := Metric.mem_closure_iff.1 hmem δ hδpos
    have hbs : ∀ x, |s x - b x| ≤ δ := fun x => by
      have h1 := ContinuousMap.dist_apply_le_dist (f := s') (g := b) x
      rw [Real.dist_eq] at h1
      exact h1.trans hb.le
    have hbA : (b : 𝕋 → ℝ) ∈ 𝒜c := AC_mem_A₀ hbAC
    have hbbA : (fun x => b x * b x) ∈ 𝒜c := by
      have := mul_mem hbA hbA
      exact this
    have hbb0 : 0 ≤ᵐ[μ₀] (fun x => b x * b x) := Eventually.of_forall fun x => mul_self_nonneg _
    have hpair := h _ hbbA hbb0
    have hdiff : ∀ x, |m x - b x * b x| ≤ δ * (2 * M + 1) := by
      intro x
      have e : m x - b x * b x = (s x - b x) * (s x + b x) := by rw [← hs2 x]; ring
      rw [e, abs_mul]
      have h1 := hbs x
      have h2 : |s x + b x| ≤ 2 * M + 1 := by
        have : |b x| ≤ |s x| + |s x - b x| := by
          calc |b x| = |s x - (s x - b x)| := by ring_nf
            _ ≤ |s x| + |s x - b x| := abs_sub _ _
        calc |s x + b x| ≤ |s x| + |b x| := abs_add_le _ _
          _ ≤ 2 * M + 1 := by linarith [hsM x]
      exact mul_le_mul h1 h2 (abs_nonneg _) hδpos.le
    have hic : Continuous fun x => b x * b x * f x := (b.continuous.mul b.continuous).mul hfc
    have hint1 : Integrable (fun x => b x * b x * f x) μ₀ := integrable_of_cont hic
    have hint2 : Integrable (fun x => (m x) ^ 2) μ₀ := integrable_of_cont (hmc.pow 2)
    have hint3 : Integrable (fun x => (m x - b x * b x) * f x) μ₀ :=
      integrable_of_cont ((hmc.sub (b.continuous.mul b.continuous)).mul hfc)
    have hsplit : ∀ x, -(m x) ^ 2 = b x * b x * f x + (m x - b x * b x) * f x := fun x => by
      rw [← hmf x]; ring
    have h4 : ∫ x, -(m x) ^ 2 ∂μ₀ = ∫ x, b x * b x * f x ∂μ₀ + ∫ x, (m x - b x * b x) * f x ∂μ₀ := by
      rw [← integral_add hint1 hint3]
      exact integral_congr_ae (Eventually.of_forall hsplit)
    have h5 : ∫ x, -((m x - b x * b x) * f x) ∂μ₀ ≤ ∫ x, (ε : ℝ) ∂μ₀ := by
      refine integral_mono hint3.neg (integrable_const _) (fun x => ?_)
      have h6 : |(m x - b x * b x) * f x| ≤ δ * (2 * M + 1) * K := by
        rw [abs_mul]; exact mul_le_mul (hdiff x) (hfK x) (abs_nonneg _) (by positivity)
      have h7 : δ * (2 * M + 1) * K ≤ ε := by
        have : δ * (2 * M + 1) * K ≤ δ * ((2 * M + 1) * (K + 1)) := by
          have : 0 ≤ δ * (2 * M + 1) := by positivity
          nlinarith
        linarith
      have := neg_abs_le ((m x - b x * b x) * f x)
      simp only [] at *
      linarith
    have hconst : ∫ x : 𝕋, (ε : ℝ) ∂μ₀ = ε := by simp
    rw [hconst] at h5
    rw [integral_neg] at h5
    rw [integral_neg] at h4
    beta_reduce at hpair
    linarith
  have h0 : ∫ x, (m x) ^ 2 ∂μ₀ ≤ 0 := le_of_forall_pos_le_add (fun ε hε => by
    have := key ε hε; linarith)
  have hint2 : Integrable (fun x => (m x) ^ 2) μ₀ := integrable_of_cont (hmc.pow 2)
  have h00 : ∫ x, (m x) ^ 2 ∂μ₀ = 0 :=
    le_antisymm h0 (integral_nonneg fun x => sq_nonneg _)
  have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (m x)) hint2).1 h00
  filter_upwards [this] with x hx
  have : (m x) ^ 2 = 0 := hx
  have hmx : m x = 0 := by simpa using this
  have : -f x ≤ 0 := by
    have := le_max_left (-f x) 0
    rw [show max (-f x) 0 = m x from rfl, hmx] at this
    exact this
  simp only [Pi.zero_apply]
  linarith

end MarkovTriple.BGL.Circle
