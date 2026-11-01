import MarkovTriple.BGL.Instances.OU.Full
import MarkovTriple.BGL.Instances.Circle.Triple
import MarkovTriple.BGL.Theory.Poincare
import MarkovTriple.BGL.Theory.ESAOne
import MarkovTriple.BGL.Theory.Tests

/-! Stage-3 hostile probes (NOT imported by root). -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open MarkovTriple.BGL MarkovTriple.BGL.Instances.OU MarkovTriple.BGL.Circle

namespace MarkovTriple.BGL.Audit3

instance : IsProbabilityMeasure ouFull.μ :=
  (inferInstance : IsProbabilityMeasure (gaussianReal 0 1))

/-- Gaussian Poincare PI(1), fully unfolded, for C_c^infty functions. -/
theorem gaussian_poincare (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    variance f (gaussianReal 0 1) ≤ ∫ x, (deriv f x) ^ 2 ∂(gaussianReal 0 1) := by
  have h := FullTriple.poincare_of_CD_infty ouFull one_pos ouFull_CD
  have h2 := h.2.2 f ⟨hf, hc⟩
  have e : ∀ x, ouFull.Γ f f x = deriv f x * deriv f x := fun x => rfl
  simp only [energy, dirichletForm, e] at h2
  have : ouFull.μ = gaussianReal 0 1 := rfl
  rw [this] at h2
  simpa [sq] using h2

/-- conservative_of_esa on circle. -/
example (t : ℝ≥0) : letI : IsFiniteMeasure circleCompact.toDiffusionTriple.μ :=
    inferInstanceAs (IsFiniteMeasure MarkovTriple.Sanity.Circle.μ₀)
    circleCompact.toDiffusionTriple.semigroup t circleCompact.toDiffusionTriple.one2
      = circleCompact.toDiffusionTriple.one2 :=
  haveI : IsFiniteMeasure circleCompact.toDiffusionTriple.μ :=
    inferInstanceAs (IsFiniteMeasure MarkovTriple.Sanity.Circle.μ₀)
  DiffusionTriple.semigroup_one2 _ circleCompact.esaProp t

/-- S11 for the OU triple, derived from ESA alone (no `conservative` field used), along the
explicit exhaustion `expo`. -/
theorem ou_conservative_via_esa (t : ℝ≥0) :
    ∀ᵐ x ∂ouDiff.μ, Filter.Tendsto
      (fun n => (ouDiff.semigroup t (ouDiff.cls ⟨expo n, ⟨expo_sm n, expo_cs n⟩⟩) : ℝ → ℝ) x)
      Filter.atTop (nhds 1) :=
  DiffusionTriple.conservative_of_esa ouDiff (fun u hu => ou_esa_core u hu)
    (u := expo) ⟨fun n => ⟨expo_sm n, expo_cs n⟩,
      fun n => Filter.Eventually.of_forall fun x => expo_mono x (Nat.le_succ n),
      Filter.Eventually.of_forall expo_tendsto⟩ t

end MarkovTriple.BGL.Audit3
#print axioms MarkovTriple.BGL.Audit3.gaussian_poincare
#print axioms MarkovTriple.BGL.Audit3.ou_conservative_via_esa
