import MarkovTriple.Stochastic.R23.Lebesgue
import MarkovTriple.Stochastic.OUFull

/-! Axiom audit of Round 23, Stream S (see `STATEMENTS_R23_S.md`). -/

#print axioms MarkovTriple.Stochastic.R23.abs_le_norm_of_aeLinear
#print axioms MarkovTriple.Stochastic.R23.exists_kernel_of_aeLinear
#print axioms MarkovTriple.Stochastic.R23.tendsto_tr
#print axioms MarkovTriple.Stochastic.R23.exists_kernel_of_posContraction_locFinite
#print axioms MarkovTriple.Stochastic.R23.lintegral_P_le
#print axioms MarkovTriple.Stochastic.R23.bind_le_of_rep
#print axioms MarkovTriple.Stochastic.R23.exists_kernel_of_posContraction_locFinite_subInv
#print axioms MarkovTriple.Stochastic.R23.cc_dense
#print axioms MarkovTriple.Stochastic.R23.ncKernelRepInf
#print axioms MarkovTriple.Stochastic.R23.ncKernelRepInf_subInvariant
#print axioms MarkovTriple.Stochastic.R23.ncKernelRepInf_C0
#print axioms MarkovTriple.Stochastic.R23.ncKernelRepInf_univ_ae
#print axioms MarkovTriple.Stochastic.R23.exists_markovRep
#print axioms MarkovTriple.Stochastic.R23.lebesgueKernelRep
#print axioms MarkovTriple.Stochastic.R23.lebesgueKernelRep_subInvariant
#print axioms MarkovTriple.Stochastic.R23.lebesgue_exists_markovRep

-- the infinite-`μ` construction also covers the finite OU triple (sanity check)
open MarkovTriple.BGL.Instances.OU in
noncomputable example : MarkovTriple.Stochastic.KernelRepresentation ouDiff :=
  MarkovTriple.Stochastic.R23.ncKernelRepInf ouDiff
