import MarkovTriple.FunctionalInequalities.Poincare
import MarkovTriple.Sanity.Trivial

/-! # Phase-4 audit (1): the hypotheses of `poincare_of_CD_infty` are jointly satisfiable.

Degenerate witness: the one-point probability space with `Γ = 0`, `L = 0` (`Sanity.trivialFull`):
a `FullMarkovTriple` with probability measure, `CD(ρ,∞)` for every `ρ` (so `ρ = 1 > 0`), and
`ErgodicL2` (`L²` is one-dimensional).  So the theorem is not vacuous *as stated*; it is only
exercised with `Γ = 0` here.  A witness with `Γ ≠ 0` and `ρ > 0` (S^n / Legendre / OU) is NOT in the
library. -/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.Audit

noncomputable def onePt : FullMarkovTriple Unit := Sanity.trivialFull (Measure.dirac ())

instance : IsProbabilityMeasure onePt.μ := by
  show IsProbabilityMeasure (Measure.dirac ())
  infer_instance

theorem onePt_CD : onePt.toMarkovTriple.CD 1 ∞ := Sanity.trivialTriple_CD _ 1 (by simp)

theorem onePt_ergodic : onePt.toMarkovTriple.ErgodicL2 := by
  intro u _
  refine ⟨(u : Unit → ℝ) (), ?_⟩
  show (u : Unit → ℝ) =ᵐ[Measure.dirac ()] fun _ => (u : Unit → ℝ) ()
  rw [ae_dirac_eq]

/-- `poincare_of_CD_infty` can be applied: hypotheses jointly satisfiable (degenerately). -/
theorem onePt_PI : onePt.toMarkovTriple.PoincareIneq (1 / 1) :=
  Hilbert.poincare_of_CD_infty onePt one_pos onePt_CD onePt_ergodic

#print axioms onePt_PI
end MarkovTriple.Audit
