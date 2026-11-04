import MarkovTriple.BGL.Instances.Gibbs.Core2PolyExample

/-! Axiom audit of R19 Stream A4 (Gibbs `Core2` beyond `GrowHess`; only `propext`, `Classical.choice`, `Quot.sound`). -/
open MarkovTriple.BGL.Instances.Gibbs
#print axioms GibbsData.hardy_ibp_w
#print axioms GibbsData.memLp_of_BE_w
#print axioms GibbsData.memLp_of_hardy_w
#print axioms GibbsData.GrowHess.polyHess
#print axioms GibbsData.resolvent_pow_L2
#print axioms GibbsData.resolvent_weighted_L2_poly
#print axioms GibbsData.cutoff_ZL_p
#print axioms GibbsData.gibbsFull_core2_of_polyHess
#print axioms GibbsData.gibbsFull_core2_of_growHess_via_poly
#print axioms GibbsData.gibbs_mem_domain_of_Γ₂_polyHess
#print axioms GibbsData.gibbs_mem_domain_of_Γ₂_convex
#print axioms expGibbs_convex
#print axioms expGibbs_polyHess
#print axioms expGibbs_not_growHess
#print axioms expGibbs_core2
#print axioms expGibbs_mem_domain_of_Γ₂
