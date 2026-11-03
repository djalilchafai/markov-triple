import MarkovTriple.BGL.Instances.GibbsRd.EllipticDefs
import MarkovTriple.BGL.Instances.GibbsRd.EllipticDiffQuot
import MarkovTriple.BGL.Instances.GibbsRd.EllipticCaccioppoli
import MarkovTriple.BGL.Instances.GibbsRd.EllipticQ3
import MarkovTriple.BGL.Instances.GibbsRd.EllipticLocal
import MarkovTriple.BGL.Instances.GibbsRd.EllipticMollify
import MarkovTriple.BGL.Instances.GibbsRd.EllipticWeakForm
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE2Pre

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
#print axioms Elliptic.abs_integral_mul_le
#print axioms Elliptic.weakDeriv_translate
#print axioms Elliptic.norm_le_of_dual_bound
#print axioms Elliptic.hasDerivAt_shift_integral
#print axioms Elliptic.eLpNorm_dq_le
#print axioms Elliptic.weakDeriv_of_local
#print axioms Elliptic.weakDeriv_of_local_dq
#print axioms Elliptic.abs_dq_le
#print axioms Elliptic.exists_mollifier
#print axioms Elliptic.moll_contDiff
#print axioms Elliptic.moll_hasCompactSupport
#print axioms Elliptic.pderiv_moll
#print axioms Elliptic.moll_memLp_norm_le
#print axioms Elliptic.moll_tendsto
#print axioms Elliptic.tendsto_integral_mul
#print axioms Elliptic.weakDeriv_zero_off
#print axioms Elliptic.moll_eq_zero_off
#print axioms EllData.weakForm_of_veryWeak
#print axioms EllData.weakForm_extend
#print axioms Elliptic.weakDeriv_dq
#print axioms Elliptic.dq_ibp_L2
#print axioms Elliptic.dq_local_bound
