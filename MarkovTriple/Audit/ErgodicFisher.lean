import Mathlib
import MarkovTriple.Frozen.Ergodic
import MarkovTriple.Frozen.Fisher
import MarkovTriple.Frozen.Poincare
import MarkovTriple.Frozen.LSI
import MarkovTriple.Frozen.CDFull
import MarkovTriple.Sanity.Trivial

open MeasureTheory Filter
open scoped Topology ENNReal

namespace MarkovTriple.Audit

variable {E : Type*} [MeasurableSpace E]

/-! ## (b) the zero measure: ergodic, `CD ρ ∞` for all ρ, but neither PI nor LSI
(they demand `IsProbabilityMeasure`).  So any `CD ⇒ PI/LSI` theorem needs `IsProbabilityMeasure μ`
as an explicit hypothesis; `Ergodic` does not provide it, and neither does the structure
(only finiteness, in fact not even nonzero). -/

noncomputable def T0 : MarkovTriple Bool := Sanity.trivialTriple (0 : Measure Bool)

theorem T0_ergodic : T0.ErgodicL2 := fun u _ => ⟨0, by
  have : T0.μ = 0 := rfl
  exact (ae_iff.2 (by simp [this]))⟩

theorem T0_CD (ρ : ℝ) : T0.CD ρ ∞ := Sanity.trivialTriple_CD _ ρ (by simp)

theorem T0_not_PI (C : ℝ) : ¬ T0.PoincareIneq C := fun h => by
  have := h.1
  have h2 := this.measure_univ
  simp [T0, Sanity.trivialTriple] at h2

theorem T0_not_LSI (C : ℝ) : ¬ T0.LogSobolevIneq C := fun h => by
  have := h.1
  have h2 := this.measure_univ
  simp [T0, Sanity.trivialTriple] at h2

/-! ## (d) Fisher -/

theorem L_one (T : MarkovTriple E) : T.L 1 = 0 := by
  have := (T.diffusion 0 (fun _ => (1 : ℝ)) contDiff_const (fun i => Fin.elim0 i) (fun i => i.elim0)
    (by exact T.A₀.one_mem)).2
  funext x
  have h := congrFun this x
  have h' : T.L 1 x = 0 := by
    have : T.L (fun _ => (1:ℝ)) x = 0 := by simpa using h
    exact this
  simpa using h'

theorem Γ_one (T : MarkovTriple E) : T.Γ 1 1 = 0 := by
  funext x
  have := T.carre_du_champ 1 T.A₀.one_mem 1 T.A₀.one_mem x
  rw [mul_one, L_one] at this
  simpa using this

/-- `h = 1` is Fisher-admissible in every triple and `I(1) = 0`. -/
theorem fisher_one (T : MarkovTriple E) : T.IsFisherAdmissible 1 ∧ T.fisherInfo 1 = 0 := by
  refine ⟨⟨Filter.Eventually.of_forall fun x => by simp, ?_⟩, ?_⟩
  · simp [Γ_one]
  · simp [fisherInfo, Γ_one]

/-- On the zero measure every `h` is admissible (vacuous): harmless, but note admissibility alone
says nothing about `h ∈ 𝒜₀`. -/
theorem fisher_zero_measure (h : Bool → ℝ) : T0.IsFisherAdmissible h := by
  refine ⟨?_, ?_⟩ <;> simp [T0, Sanity.trivialTriple]

end MarkovTriple.Audit
#print axioms MarkovTriple.Audit.fisher_one
#print axioms MarkovTriple.Audit.T0_ergodic
