import MarkovTriple.BGL.Instances.Gibbs.DirectOld
import MarkovTriple.BGL.Instances.GibbsRd.DirectExample

/-! Axiom audit of R20 Stream D1 (direct converse of Prop. 3.3.17 without `Core2`; only `propext`, `Classical.choice`, `Quot.sound`). -/
open MarkovTriple.BGL.Instances.Gibbs
open MarkovTriple.BGL.Instances.GibbsRd
#print axioms direct_pt
#print axioms GibbsData.memLp_Lg_of_Γ₂
#print axioms GibbsData.gibbs_mem_domain_of_Γ₂_direct
#print axioms spk_peak
#print axioms spikyGibbs_convex
#print axioms spikyGibbs_not_polyHess
#print axioms spikyGibbs_mem_domain_of_Γ₂
#print axioms spikyGibbs_memLp_id
#print axioms spikyGibbs_id_mem_domain
#print axioms expGibbs_mem_domain_of_Γ₂_direct
#print axioms quarGibbs_mem_domain_of_Γ₂_direct
#print axioms cosGibbs_mem_domain_of_Γ₂_direct
#print axioms rd_pt
#print axioms sum_cross
#print axioms GibbsRdData.memLp_Lr_of_Γ₂
#print axioms GibbsRdData.gibbsRd_mem_domain_of_Γ₂_direct
#print axioms hessGe_spkVd
#print axioms spikyData_not_growHess3
#print axioms spikyData_witness
#print axioms spikyData_mem_domain_of_Γ₂
