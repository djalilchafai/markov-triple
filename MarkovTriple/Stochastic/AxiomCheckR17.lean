import MarkovTriple.Stochastic.FellerMeasurable
import MarkovTriple.Stochastic.FellerProcessBridge
import MarkovTriple.Stochastic.ExactCK

/-! Axiom audit of the round-17 stochastic layer (see `STATEMENTS_R17.md`). -/

#print axioms MarkovTriple.Stochastic.measurable_of_integrals_param
#print axioms MarkovTriple.Stochastic.clsC_le_iff
#print axioms MarkovTriple.Stochastic.isClosed_fellerOp_ball
#print axioms MarkovTriple.Stochastic.measurable_fellerOp_time
#print axioms MarkovTriple.Stochastic.measurable_fellerOp_joint
#print axioms MarkovTriple.Stochastic.fellerKernel_measurable_joint
#print axioms MarkovTriple.Stochastic.fellerMarkovProcessData
#print axioms MarkovTriple.Stochastic.fellerMarkovProcessBridge
#print axioms MarkovTriple.Stochastic.fellerMarkovProcessBridge_kernel
#print axioms MarkovTriple.Stochastic.Sphere.sphereMarkovProcessBridge
#print axioms MarkovTriple.Stochastic.Sphere.sphereMarkovProcessBridge_kernel
#print axioms MarkovTriple.Stochastic.Sphere.sphereMarkovProcessBridge_isMarkov
#print axioms MarkovTriple.Stochastic.ae_measure_eq_of_forall
#print axioms MarkovTriple.Stochastic.KernelRepresentation.kappa_zero_ae
#print axioms MarkovTriple.Stochastic.KernelRepresentation.measurableSet_shrink
#print axioms MarkovTriple.Stochastic.KernelRepresentation.measure_shrink_compl
#print axioms MarkovTriple.Stochastic.KernelRepresentation.iterShrink_good
#print axioms MarkovTriple.Stochastic.KernelRepresentation.exists_exact_ck
#print axioms MarkovTriple.Stochastic.rieszKernel_exists_exact_ck
