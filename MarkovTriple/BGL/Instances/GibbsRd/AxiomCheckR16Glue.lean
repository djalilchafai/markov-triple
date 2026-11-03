import MarkovTriple.BGL.Instances.GibbsRd.EllRegProof
import MarkovTriple.BGL.Instances.GibbsRd.Unconditional
import MarkovTriple.BGL.Instances.Riemannian.Unconditional

/-! Axiom audit of R16 glue (only `propext`, `Classical.choice`, `Quot.sound`). -/
open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL.Instances.Riemannian
#print axioms EllData.veryWeakSol_of_mu
#print axioms EllData.chain_sobolev
#print axioms EllData.ellReg
#print axioms EllData.weakHypo_unconditional
#print axioms EllData.f8_unconditional
#print axioms GibbsRdData.gibbsRd_poincare_unconditional
#print axioms GibbsRdData.gibbsRd_spectralGap_unconditional
#print axioms GibbsRdData.gibbsRd_expDecay_unconditional
#print axioms GibbsRdData.gibbsRdFull_CD_unconditional
#print axioms GibbsRdData.gibbsRdFull_poincare_unconditional
#print axioms GibbsRdData.gibbsRdFull_logSobolev_unconditional
#print axioms GibbsRdData.gibbsRdFull_gradient_bound_noHyp
#print axioms GibbsRdData.gibbsRdFull_hasGradientBound_unconditional
#print axioms RiemData.riem_poincare_unconditional
#print axioms RiemData.riemFull_logSobolev_unconditional
#print axioms RiemData.riemFull_gradient_bound_unconditional
#print axioms RiemData.riemFull_hasGradientBound_unconditional
#print axioms confRiem_poincare_unconditional
#print axioms confRiem_spectralGap_unconditional
#print axioms confRiem_expDecay_unconditional
#print axioms confRiem_CD_unconditional
#print axioms confRiem_logSobolev_unconditional
#print axioms confRiem_hasGradientBound_unconditional
