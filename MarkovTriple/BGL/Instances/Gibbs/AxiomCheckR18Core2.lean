import MarkovTriple.BGL.Instances.Gibbs.Core2WExample

/-! Axiom audit of R18 Stream A2 (Gibbs `Core2` without bounded `V'`; only `propext`, `Classical.choice`, `Quot.sound`). -/
open MarkovTriple.BGL.Instances.Gibbs
#print axioms GibbsData.hardy_ibp
#print axioms GibbsData.memLp_of_BE
#print axioms GibbsData.memLp_of_hardy
#print axioms GibbsData.resolvent_weighted_L2
#print axioms GibbsData.cutoff_ZL_w
#print axioms GibbsData.gibbsFull_core2_of_growHess
#print axioms GibbsData.gibbsFull_core2_of_bddHess
#print axioms GibbsData.gibbs_mem_domain_of_Γ₂_growHess
#print axioms GibbsData.gibbs_mem_domain_of_Γ₂_bddHess
#print axioms cosGibbs_bddHess
#print axioms cosGibbs_convex
#print axioms cosGibbs_not_bddJet
#print axioms cosGibbs_core2
#print axioms cosGibbs_mem_domain_of_Γ₂
#print axioms quarGibbs_convex
#print axioms quarGibbs_growHess
#print axioms quarGibbs_not_bddHess
#print axioms quarGibbs_core2
#print axioms quarGibbs_mem_domain_of_Γ₂
