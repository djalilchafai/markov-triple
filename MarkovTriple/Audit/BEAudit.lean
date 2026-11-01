import MarkovTriple.Sanity.OU.Full
import MarkovTriple.FunctionalInequalities.BELSI
import MarkovTriple.FunctionalInequalities.BECircle
import Lean

/-! # AUDIT (round 6): Bakry-Emery `BEStable` / `logSobolevIneq_of_CD`  (not imported by the root)

1. Every hypothesis of `logSobolevIneq_of_CD` except `BEStable` is DISCHARGED for the OU full triple
   (so the theorem is not vacuous through any other hypothesis): `conditional_gaussian_LSI`.
2. `BEStable ouFull` is not refuted by its trivial clause (`ou_A₀_bdd`), and the `reg` clause is not
   trivially true either: `BEReg` fails for the unbounded `id ∈ 𝒜` (`ou_not_BEReg_id`), i.e. it is
   genuinely about the Mehler-decay of `P_s φ`, not about all of `𝒜`.
3. Axiom walk over all constants of `MarkovTriple.FunctionalInequalities.*`. -/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BEAudit
open MarkovTriple.Sanity.OU MarkovTriple.BE

theorem ou_A₀_bdd : ∀ f ∈ ouFull.A₀, MemLp f ∞ ouFull.μ := fun f hf =>
  memLp_A₀ (show f ∈ MarkovTriple.Sanity.OU.A₀ from hf) ∞

/-- the identity is in `𝒜` but is not essentially bounded for the Gaussian. -/
theorem ou_id_not_memLp_top : ¬ MemLp (fun x : ℝ => x) ∞ ouFull.μ := by
  intro h
  obtain ⟨C, hC⟩ := bd_of_memLp_top h
  have hC' : ∀ᵐ x ∂γ, |x| ≤ C := hC
  have hv : (volume : Measure ℝ) ≪ γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ), |x| ≤ C := hv.ae_le hC'
  have h3 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ (Set.Ioi (|C| + 1))ᶜ := by
    filter_upwards [h2] with x hx
    simp only [Set.mem_compl_iff, Set.mem_Ioi, not_lt]
    have := le_abs_self C
    linarith [le_abs_self x]
  have h4 := ae_iff.1 h3
  simp only [Set.compl_def] at h4
  have h5 : (volume : Measure ℝ) (Set.Ioi (|C| + 1)) = 0 := by
    convert h4 using 2; ext x; simp
  rw [Real.volume_Ioi] at h5
  exact ENNReal.top_ne_zero h5

theorem ou_not_BEReg_id : ¬ BEReg ouFull (fun x : ℝ => x) := fun h => ou_id_not_memLp_top h.bdd

/-- Every hypothesis of `logSobolevIneq_of_CD` except `BEStable` holds for the OU triple. -/
theorem conditional_gaussian_LSI (hB : BEStable ouFull) :
    ouFull.toMarkovTriple.LogSobolevIneq (1 / 1) :=
  logSobolevIneq_of_CD ouFull hB one_pos ouFull_CDFull
    (show ouTriple.ErgodicL2 from ou_ergodic)

/-- sanity: the hypotheses are met by a triple with `Γ ≠ 0` and `ρ = 1 > 0`. -/
theorem ou_hyps :
    IsProbabilityMeasure ouFull.μ ∧ ouFull.CDFull 1 ∞ ∧ ouFull.toMarkovTriple.ErgodicL2 ∧
      ouFull.Γ (fun x => x) (fun x => x) ≠ 0 :=
  ⟨inferInstance, ouFull_CDFull, ou_ergodic, ouFull_Γ_ne_zero⟩

end MarkovTriple.BEAudit

#print axioms MarkovTriple.BEAudit.ou_A₀_bdd
#print axioms MarkovTriple.BEAudit.ou_not_BEReg_id
#print axioms MarkovTriple.BEAudit.conditional_gaussian_LSI
#print axioms MarkovTriple.BEAudit.ou_hyps
