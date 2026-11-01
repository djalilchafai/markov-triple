import Mathlib
import MarkovTriple.FunctionalInequalities.BELSI
import MarkovTriple.Sanity.CircleFull

/-! # Bakry–Émery (Phase 4b) on the circle: `BEStable circleFull` and the second-order inequality

The circle `(𝕋, Haar)` with `𝒜 = 𝒜₀ = C^∞(𝕋)`, `L f = f''`, `Γ(f,g) = f'g'` is a genuine full
Markov triple with `Γ ≠ 0` (`Sanity/CircleFull.lean`).  It satisfies `CD(0,∞)` only (no `ρ > 0`), so
`logSobolevIneq_of_CD` (which needs `ρ > 0`) does not apply; but the whole interpolation machinery
(regular representative, `L²`-calculus, `Γ`-calculus) does, with `ρ = 0`: along the flow
`q = (d/ds) Ent(ε + P_s φ)` is differentiable with `q' ≥ 0`, i.e. the Fisher information is
non-increasing. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace MarkovTriple.BE

open MarkovTriple.Sanity.Circle

theorem circle_BEStable : BEStable circleFull := by
  refine BEStable.of_A_eq_A₀ circleFull (fun f hf => mem_Afull.1 hf) ?_
  intro f hf
  have hc : Continuous f := continuous_of_A₀ hf
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact memLp_top_of_bound hc.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))

theorem circleFull_CDFull_zero : circleFull.CDFull 0 ∞ :=
  ⟨by simp, fun f hf => (circle_CD (le_refl (0 : ℝ)) (le_top : (1 : ℝ≥0∞) ≤ ∞)).2 f
    (mem_Afull.1 hf)⟩

instance : IsProbabilityMeasure circleFull.μ := (inferInstance : IsProbabilityMeasure μ₀)

/-- **Second-order Bakry–Émery inequality on the circle** (`ρ = 0`): the Fisher information along
the heat flow is non-increasing (`q' ≥ 0`). -/
theorem circle_second_order {φ : 𝕋 → ℝ} (hφ : φ ∈ circleFull.A₀)
    (h0 : 0 ≤ᵐ[circleFull.μ] φ) {M : ℝ} (hM : 0 < M) (hb : ∀ᵐ x ∂circleFull.μ, |φ x| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (C : Cut ε M) {s : ℝ} (hs : 0 < s) :
    ∃ q' : ℝ, HasDerivAt (qFun circleFull hφ C) q' s ∧ 0 ≤ q' := by
  obtain ⟨q', h1, h2⟩ := exists_deriv_qFun circleFull circle_BEStable circleFull_CDFull_zero hφ h0
    hM hb hε C hs
  exact ⟨q', h1, by simpa using h2⟩

/-- the hypotheses of `circle_second_order` are satisfiable by a test function with `Γ ≠ 0`. -/
example : ∃ φ : 𝕋 → ℝ, ∃ hφ : φ ∈ circleFull.A₀, 0 ≤ᵐ[circleFull.μ] φ ∧
    (∀ᵐ x ∂circleFull.μ, |φ x| ≤ 2) ∧ circleFull.Γ φ φ ≠ 0 := by
  have hc : ⇑cC ∈ circleFull.A₀ := by
    show ⇑cC ∈ MarkovTriple.Sanity.Circle.A₀
    exact mc_mem 1
  have hcA : ⇑cC ∈ circleFull.A := circleFull.A₀_le _ hc
  have hone : (fun _ : 𝕋 => (1 : ℝ)) ∈ circleFull.A := circleFull.A.one_mem
  have hsum : (fun x => 1 + cC x) ∈ circleFull.A := circleFull.A.add_mem hone hcA
  have hre : ∀ x : 𝕋, |cC x| ≤ 1 := fun x => by
    have h : ‖fourier (1 : ℤ) x‖ = 1 := by simp [fourier_apply]
    have := Complex.abs_re_le_norm (fourier (1 : ℤ) x)
    rw [h] at this
    exact this
  refine ⟨fun x => 1 + cC x, mem_Afull.1 hsum,
    Filter.Eventually.of_forall fun x => ?_, Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · have := (abs_le.1 (hre x)).1
    show 0 ≤ 1 + cC x
    linarith
  · have := abs_le.1 (hre x)
    show |1 + cC x| ≤ 2
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  · rw [Γ_const_add circleFull hcA 1]
    exact circleFull_Γ_ne_zero

end MarkovTriple.BE
