import MarkovTriple.Sanity.OU.BEReg
import MarkovTriple.FunctionalInequalities.BELSI
import MarkovTriple.Hilbert.FullBridge

/-! # OU (Part 20): `BEStable ouFull` and the Gaussian log-Sobolev inequality -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Real SchwartzMap

namespace MarkovTriple.Sanity.OU

instance : γ.IsOpenPosMeasure :=
  ⟨fun _U hU hne h0 => hU.measure_ne_zero volume hne
    ((ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero) h0)⟩

/-- **`BEStable` for the Ornstein–Uhlenbeck full triple.** -/
theorem ouFull_BEStable : BE.BEStable ouFull := by
  refine ⟨fun f hf => ?_, ?_⟩
  · obtain ⟨C, hC⟩ := A₀.bdd hf
    exact memLp_top_of_bound hf.1.continuous.aestronglyMeasurable C (ae_of_all _ fun x => by simpa using hC x)
  · intro φ hφ s hs g hg hae ψ hψ
    have hP := Hilbert.isSemigroupOf_full ouFull
    have hm := mehler_ae hP s hφ (BE.cl ouFull hφ) (BE.coeFn_cl ouFull hφ)
    have hae' : g =ᵐ[γ] Mh (Real.exp (-(s : ℝ))) (√(1 - Real.exp (-(s : ℝ)) ^ 2)) φ :=
      (hae.symm).trans hm
    have ha0 : 0 < Real.exp (-(s : ℝ)) := Real.exp_pos _
    have hc1 : |√(1 - Real.exp (-(s : ℝ)) ^ 2)| ≤ 1 := by
      have : Real.exp (-(s : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.2 (by nlinarith)
    have hgeq : g = Mh (Real.exp (-(s : ℝ))) (√(1 - Real.exp (-(s : ℝ)) ^ 2)) φ :=
      (Continuous.ae_eq_iff_eq γ (show Sm g from hg).continuous
        (sm_Mh _ _ hφ).continuous).1 hae'
    have := beReg_comp_schwartz (mehlerS ha0 _ hc1 hφ) hψ
    rw [hgeq]
    exact this

/-- **The Gaussian logarithmic Sobolev inequality** `Ent_γ(f²) ≤ 2 ℰ(f)` for `f ∈ C_c^∞(ℝ)`
(frozen normalisation `LogSobolevIneq (1/1)`), obtained end-to-end from the abstract
Bakry–Émery theorem `BE.logSobolevIneq_of_CD` with `ouFull_CDFull`, `ou_ergodic` and
`ouFull_BEStable`. -/
theorem ou_lsi : ouFull.toMarkovTriple.LogSobolevIneq (1 / 1) :=
  BE.logSobolevIneq_of_CD ouFull ouFull_BEStable one_pos ouFull_CDFull ou_ergodic

end MarkovTriple.Sanity.OU

#print axioms MarkovTriple.Sanity.OU.mehler_ae
#print axioms MarkovTriple.Sanity.OU.ouFull_BEStable
#print axioms MarkovTriple.Sanity.OU.ou_lsi
