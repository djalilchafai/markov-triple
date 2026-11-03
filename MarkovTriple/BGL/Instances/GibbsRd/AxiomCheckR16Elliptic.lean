import MarkovTriple.BGL.Instances.GibbsRd.EllipticDefs
import MarkovTriple.BGL.Instances.GibbsRd.EllipticDiffQuot
import MarkovTriple.BGL.Instances.GibbsRd.EllipticCaccioppoli

/-! Axiom audit of the R16 elliptic half (only `propext`, `Classical.choice`, `Quot.sound`). -/
open MarkovTriple.BGL.Instances.GibbsRd
#print axioms Elliptic.LocL2.locallyIntegrable
#print axioms Elliptic.WeakDeriv.unique
#print axioms Elliptic.ibp_smooth
#print axioms Elliptic.weakDeriv_of_smooth
#print axioms Elliptic.WeakDeriv.add
#print axioms Elliptic.WeakDeriv.const_mul
#print axioms Elliptic.WeakDeriv.smooth_mul
#print axioms Elliptic.LocL2.of_smooth
#print axioms Elliptic.Sobolev.mono
#print axioms Elliptic.Sobolev.add
#print axioms Elliptic.Sobolev.of_smooth
#print axioms Elliptic.Sobolev.smooth_mul
#print axioms Elliptic.dq_ibp
#print axioms Elliptic.memLp_dq
#print axioms Elliptic.dq_pointwise
#print axioms Elliptic.dq_tendsto
#print axioms Elliptic.weak_subseq
#print axioms Elliptic.weakDeriv_of_bounded_dq
#print axioms EllData.Γ_mul_left
#print axioms EllData.Γ_young
#print axioms EllData.caccioppoli_identity
#print axioms EllData.caccioppoli
#print axioms Elliptic.WeakDeriv.congr_ae
#print axioms Elliptic.Sobolev.congr_ae
