import Mathlib
import MarkovTriple.Sanity.Trivial

/-!
# AUDIT: the frozen definitions admit non-ergodic "Markov triples" with CD(ρ,∞) for all ρ
but neither PI nor LSI.  Two-point space, uniform measure, `L = 0`, `Γ = 0`
(the `trivialFull` of `Sanity/Trivial.lean`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovTriple.Audit

noncomputable def μ2 : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure μ2 := by unfold μ2; infer_instance

noncomputable def T2 : FullMarkovTriple Bool := Sanity.trivialFull μ2

/-- CD(ρ,∞) for every real ρ (e.g. ρ = 1 > 0), on a full Markov triple. -/
theorem T2_CD (ρ : ℝ) : T2.toMarkovTriple.CD ρ ∞ :=
  Sanity.trivialTriple_CD μ2 ρ (by simp)

private lemma μ2_single (b : Bool) : μ2 {b} = 2⁻¹ := by
  unfold μ2
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  simp [PMF.uniformOfFintype_apply]

theorem T2_not_PI (C : ℝ) : ¬ T2.toMarkovTriple.PoincareIneq C := by
  rintro ⟨-, h⟩
  have := h (fun b => if b then 1 else 0) (Set.mem_univ _)
  have e : T2.toMarkovTriple.energy (fun b : Bool => if b then (1:ℝ) else 0) = 0 := by
    simp [energy, T2, Sanity.trivialFull, Sanity.trivialTriple]
  rw [e, mul_zero] at this
  have hv : 0 < ProbabilityTheory.variance (fun b : Bool => if b then (1:ℝ) else 0) μ2 := by
    have hm : MemLp (fun b : Bool => if b then (1:ℝ) else 0) 2 μ2 := MemLp.of_discrete
    rw [ProbabilityTheory.variance_eq_sub hm]
    simp only [Pi.pow_apply]
    rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
    simp [Measure.real, μ2_single, Fintype.sum_bool]
    norm_num
  exact absurd this (not_le.mpr hv)

theorem T2_not_LSI (C : ℝ) : ¬ T2.toMarkovTriple.LogSobolevIneq C := by
  rintro ⟨-, h⟩
  have := h (fun b => if b then 1 else 0) (Set.mem_univ _)
  have e : T2.toMarkovTriple.energy (fun b : Bool => if b then (1:ℝ) else 0) = 0 := by
    simp [energy, T2, Sanity.trivialFull, Sanity.trivialTriple]
  rw [e, mul_zero] at this
  have hpos : 0 < Ent μ2 (fun b : Bool => (if b then (1:ℝ) else 0) ^ 2) := by
    unfold Ent
    rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite]
    simp [Measure.real, μ2_single, Fintype.sum_bool]
    have : Real.log 2 > 0 := Real.log_pos (by norm_num)
    nlinarith
  exact absurd this (not_le.mpr hpos)

end MarkovTriple.Audit
