import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsEll

/-! Axiom audit of the R16 Friedrichs step (only `propext`, `Classical.choice`, `Quot.sound`). -/
open MarkovTriple.BGL.Instances.GibbsRd
#print axioms Elliptic.exists_frMollSeq
#print axioms Elliptic.conv_sq_le
#print axioms Elliptic.integral_conv_sq
#print axioms Elliptic.comm_formula
#print axioms Elliptic.comm_bound
#print axioms Elliptic.integral_moll_swap
#print axioms Elliptic.test_eq
#print axioms Elliptic.energy_identity
#print axioms Elliptic.energy_est
#print axioms Elliptic.weakDeriv_of_approx
#print axioms Elliptic.cutoff_h1
#print axioms Elliptic.sobolev_one_of_veryWeak
#print axioms EllData.sobolev_one_of_veryWeak
