import MarkovTriple.Sanity.OU.Full
import Lean

/-! # Round-5 audit of the OU instance (not imported by the root).
(1) axiom walk over all non-internal constants of `MarkovTriple.Sanity.OU.*`;
(2) unfolded, concrete consequences of the instance (non-vacuity). -/

open Lean Elab Command MeasureTheory ProbabilityTheory
open MarkovTriple.Sanity.OU

namespace MarkovTriple.Audit.OU

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut flagged : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`MarkovTriple.Sanity.OU).isPrefixOf mod do continue
    total := total + 1
    if ci.isUnsafe || ci.isPartial then flagged := flagged.push n
    if let .opaqueInfo _ := ci then flagged := flagged.push n
    if let .axiomInfo _ := ci then flagged := flagged.push n
    let axs ← collectAxioms n
    let extra := axs.filter (· ∉ ok)
    unless extra.isEmpty do bad := bad.push (n, extra)
  logInfo m!"OU constants walked: {total}; nonstandard-axiom constants: {bad.size}; unsafe/partial/opaque/axiom: {flagged.size}"
  logInfo m!"{bad} {flagged}"

#print axioms ouFull
#print axioms ouFull_CDFull
#print axioms ou_ergodic
#print axioms ou_poincare

/-! ### Concrete consequences -/

/-- unfolded Gaussian Poincaré: for every `f ∈ C_c^∞`, `∫ f² − (∫ f)² ≤ ∫ f'²` w.r.t. `N(0,1)`. -/
theorem ou_poincare_unfolded {f : ℝ → ℝ} (hf : f ∈ ouFull.A₀) :
    ∫ x, f x ^ 2 ∂(gaussianReal 0 1) - (∫ x, f x ∂(gaussianReal 0 1)) ^ 2 ≤
      ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1) := by
  have h := ou_poincare.2 f hf
  have hm : MemLp f 2 (gaussianReal 0 1) := ouFull.memLp f hf 2 (by norm_num) (by simp)
  haveI : IsProbabilityMeasure (gaussianReal 0 1) := inferInstance
  rw [show ouFull.μ = gaussianReal 0 1 from rfl] at h
  rw [variance_eq_sub hm] at h
  simpa [MarkovTriple.energy, ouFull, ouTriple, Go, sq, one_div] using h

/-- the generator really is `f'' - x f'` and `Γ = f' g'` -/
example (f : ℝ → ℝ) (x : ℝ) : ouFull.L f x = deriv (deriv f) x - x * deriv f x := rfl
example (f g : ℝ → ℝ) (x : ℝ) : ouFull.Γ f g x = deriv f x * deriv g x := rfl
example : ouFull.μ = gaussianReal 0 1 := rfl
example : ouFull.A₀ = MarkovTriple.Sanity.OU.A₀ := rfl
example : IsProbabilityMeasure ouFull.μ := inferInstance

/-- `Γ(id,id) = 1`, `L id = -x` : the OU operator on the identity (id ∈ 𝒜 = C^∞, not in 𝒜₀) -/
example : ouFull.Γ (fun x => x) (fun x => x) = fun _ => 1 := by
  funext x; simp [ouFull, ouTriple, Go]
example (x : ℝ) : ouFull.L (fun x => x) x = -x := by
  simp [ouFull, ouTriple, Lo]

/-- `Γ₂(id) = 1 = ρ Γ(id)` : CD(1,∞) is sharp on the identity. -/
example (x : ℝ) : ouFull.toMarkovTriple.Γ₂ (fun x => x) x = 1 := by
  have := ou_Gamma2 (f := fun x : ℝ => x) contDiff_id x
  show ouTriple.Γ₂ (fun x => x) x = 1
  simpa using this

/-- `ErgodicL2` hypothesis is satisfiable for the constant `1` (cutoff sequence): not vacuous in
the hypothesis direction; and constants are the conclusion. -/
example : ∃ f : ℕ → ℝ → ℝ, (∀ n, f n ∈ ouFull.A₀) ∧ ∀ n, f n = cut (1 / ((n:ℝ)+1)) := by
  exact ⟨fun n => cut (1 / ((n:ℝ)+1)), fun n => ⟨cut_sm _, cut_cs (by positivity)⟩, fun _ => rfl⟩

end MarkovTriple.Audit.OU
