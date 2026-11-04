import MarkovTriple.Stochastic.R22.NonCompact
import MarkovTriple.Stochastic.R22.Obstruction

/-! Axiom audit of Round 22, Stream E3 (see `STATEMENTS_R22_E3.md`). -/

#print axioms MarkovTriple.Stochastic.R22.secondCountableOnePoint
#print axioms MarkovTriple.Stochastic.R22.Uequiv
#print axioms MarkovTriple.Stochastic.R22.exists_kernel_of_posContraction_noncompact
#print axioms MarkovTriple.Stochastic.R22.ncKernelRep
#print axioms MarkovTriple.Stochastic.R22.ncKernelRep_subInvariant
#print axioms MarkovTriple.Stochastic.R22.ncKernelRep_C0
#print axioms MarkovTriple.Stochastic.R22.nc_exists_exact_ck
#print axioms MarkovTriple.Stochastic.R22.c0_dense
#print axioms MarkovTriple.Stochastic.R22.exists_kernelRepresentation_not_exact_ck

-- non-vacuity: the non-compact construction applies to the OU triple on `ℝ` (probability `γ`)
open MarkovTriple.BGL.Instances.OU in
noncomputable example : MarkovTriple.Stochastic.KernelRepresentation ouDiff :=
  MarkovTriple.Stochastic.R22.ncKernelRep ouDiff
