import MarkovTriple.Stochastic.RepExtend
import MarkovTriple.Stochastic.OUFull
import MarkovTriple.Stochastic.Circle
import MarkovTriple.Stochastic.RieszFunctional
import MarkovTriple.Stochastic.RieszKernel
import MarkovTriple.Stochastic.RieszRep
import MarkovTriple.Stochastic.RieszMarkov
import MarkovTriple.Stochastic.MarkovProcessInterface
import MarkovTriple.BGL.Instances.Circle.Triple

/-! Axiom audit of the round-15 stochastic layer (see `STATEMENTS_R15.md`). -/

#print axioms MarkovTriple.Stochastic.lintegral_sq_kernel_le
#print axioms MarkovTriple.Stochastic.kernelRep_of_dense
#print axioms MarkovTriple.Stochastic.kernelRep_of_testClass
#print axioms MarkovTriple.Stochastic.KernelBridge.ofTestClass
#print axioms MarkovTriple.Stochastic.KernelRepresentation.kernel_null_ae
#print axioms MarkovTriple.Stochastic.KernelRepresentation.ae_unique
#print axioms MarkovTriple.Stochastic.OU.ouKernelBridge
#print axioms MarkovTriple.Stochastic.OU.ouKernelBridge_isMarkov
#print axioms MarkovTriple.Stochastic.OU.ouKernelRepresentation
#print axioms MarkovTriple.Stochastic.OU.ou_rep_full
#print axioms MarkovTriple.Stochastic.Circle.circleKernel_zero
#print axioms MarkovTriple.Stochastic.Circle.circleKernel_comp
#print axioms MarkovTriple.Stochastic.Circle.circleKernel_invariant
#print axioms MarkovTriple.Stochastic.Circle.integral_fourier_heat
#print axioms MarkovTriple.Stochastic.Circle.circleKernel_rep_trigSpan
#print axioms MarkovTriple.Stochastic.Circle.circleSemigroup
#print axioms MarkovTriple.Stochastic.Circle.circleSemigroup_isMarkov
#print axioms MarkovTriple.Stochastic.Circle.circleKernelBridge
#print axioms MarkovTriple.Stochastic.Circle.circle_rep_full
#print axioms MarkovTriple.Stochastic.exists_extend_addSubgroup
#print axioms MarkovTriple.Stochastic.exists_posFunctional
#print axioms MarkovTriple.Stochastic.exists_measure_of_pos
#print axioms MarkovTriple.Stochastic.measurable_of_integrals
#print axioms MarkovTriple.Stochastic.exists_kernel_of_posContraction
#print axioms MarkovTriple.Stochastic.bind_le_of_integral_le
#print axioms MarkovTriple.Stochastic.integral_semigroup_le
#print axioms MarkovTriple.Stochastic.rieszKernel_continuous
#print axioms MarkovTriple.Stochastic.rieszKernel_subInvariant
#print axioms MarkovTriple.Stochastic.rieszKernelRep
#print axioms MarkovTriple.Stochastic.rieszKernelRep_continuous
#print axioms MarkovTriple.Stochastic.rieszKernelRep_subInvariant
#print axioms MarkovTriple.Stochastic.compactTriple_isFiniteMeasure
#print axioms MarkovTriple.Stochastic.compactTripleKernelRep
#print axioms MarkovTriple.Stochastic.rieszKernel_univ_ae
#print axioms MarkovTriple.Stochastic.rieszKernelRep_markov
#print axioms MarkovTriple.Stochastic.MarkovProcessBridge.toKernelBridge
#print axioms MarkovTriple.Stochastic.KernelBridge.toMarkovProcessBridge
#print axioms MarkovTriple.Stochastic.ouKernel_measurable_joint
#print axioms MarkovTriple.Stochastic.ouMarkovProcessBridge
#print axioms MarkovTriple.Stochastic.circleKernel_measurable_joint
#print axioms MarkovTriple.Stochastic.circleMarkovProcessBridge

/-! Non-vacuity: the general construction applies to the circle `CompactTriple`. -/
example : Nonempty (MarkovTriple.Stochastic.KernelRepresentation
    MarkovTriple.BGL.Circle.circleCompact.toDiffusionTriple) :=
  ⟨MarkovTriple.Stochastic.compactTripleKernelRep MarkovTriple.BGL.Circle.circleCompact⟩
