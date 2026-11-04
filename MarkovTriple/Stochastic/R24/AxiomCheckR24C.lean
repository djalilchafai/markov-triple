import MarkovTriple.Stochastic.R24.OU
import MarkovTriple.Stochastic.R24.Bridge
import MarkovTriple.Stochastic.R24.Compact
import MarkovTriple.Stochastic.R24.Instances

/-! Axiom audit of Round 24, Stream C (see `STATEMENTS_R24_C.md`). -/

#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_subMarkov
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_integral_cc
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_zero
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_add
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_bind_le
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_rep
#print axioms MarkovTriple.Stochastic.R24.fellerKernelRepInf
#print axioms MarkovTriple.Stochastic.R24.fellerSemigroupInf
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_unique
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_measurable_joint
#print axioms MarkovTriple.Stochastic.R24.fellerMarkovProcessDataInf
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_reversible
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_bind
#print axioms MarkovTriple.Stochastic.R24.fellerMarkovProcessBridgeInf
#print axioms MarkovTriple.Stochastic.R24.isFeller_iff_exists_continuous_kernel
#print axioms MarkovTriple.Stochastic.R24.weakFeller_kernel_unique
#print axioms MarkovTriple.Stochastic.R24.weakFeller_zero
#print axioms MarkovTriple.Stochastic.R24.weakFeller_add
#print axioms MarkovTriple.Stochastic.R24.isFellerC0_iff_exists_C0_kernel
#print axioms MarkovTriple.Stochastic.R24.isFellerC0_of_isFeller
#print axioms MarkovTriple.Stochastic.R24.fellerKernelInf_eq_fellerKernel
#print axioms MarkovTriple.Stochastic.R24.circle_isFellerC0
#print axioms MarkovTriple.Stochastic.R24.circle_fellerKernelInf_eq
#print axioms MarkovTriple.Stochastic.R24.sphere_isFellerC0
#print axioms MarkovTriple.Stochastic.R24.ou_isFellerC0
