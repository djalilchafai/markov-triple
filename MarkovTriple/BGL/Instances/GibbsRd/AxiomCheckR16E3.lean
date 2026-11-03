import MarkovTriple.BGL.Instances.GibbsRd.EllipticE3D

/-! Axiom audit of R16 E3 (only `propext`, `Classical.choice`, `Quot.sound`). -/
open MarkovTriple.BGL.Instances.GibbsRd
#print axioms EllData.comm_identity
#print axioms EllData.veryWeakSol_deriv
#print axioms EllData.sobolev_hprime
#print axioms EllData.interior_sobolev
#print axioms EllData.interior_regularity_all_orders
#print axioms EllData.interior_smooth_rep
#print axioms EllData.veryWeakSol_of_smooth
#print axioms sobolev_iff_hasSobL2
