import MarkovTriple.Stochastic.FellerKernel
import MarkovTriple.Stochastic.CircleFeller
import MarkovTriple.Stochastic.SphereFeller
import MarkovTriple.Stochastic.FellerStandard

/-! Axiom audit of the round-16 stochastic layer (see `STATEMENTS_R16.md`). -/

#print axioms MarkovTriple.Stochastic.isFeller_of_dense
#print axioms MarkovTriple.Stochastic.integral_semigroup_eq
#print axioms MarkovTriple.Stochastic.fellerOp_add_time
#print axioms MarkovTriple.Stochastic.fellerOp_zero
#print axioms MarkovTriple.Stochastic.fellerKernel
#print axioms MarkovTriple.Stochastic.integral_fellerKernel
#print axioms MarkovTriple.Stochastic.fellerKernel_subMarkov
#print axioms MarkovTriple.Stochastic.fellerKernel_zero
#print axioms MarkovTriple.Stochastic.fellerKernel_add
#print axioms MarkovTriple.Stochastic.fellerSemigroup
#print axioms MarkovTriple.Stochastic.fellerKernel_bind_le
#print axioms MarkovTriple.Stochastic.fellerKernel_rep
#print axioms MarkovTriple.Stochastic.fellerKernel_unique
#print axioms MarkovTriple.Stochastic.fellerOp_one
#print axioms MarkovTriple.Stochastic.fellerKernel_isMarkov
#print axioms MarkovTriple.Stochastic.fellerKernel_bind
#print axioms MarkovTriple.Stochastic.fellerBridge
#print axioms MarkovTriple.Stochastic.fellerBridge_isMarkov
#print axioms MarkovTriple.Stochastic.standardSemigroup_one_fin
#print axioms MarkovTriple.Stochastic.standardFellerBridge
#print axioms MarkovTriple.Stochastic.compactFellerBridge
#print axioms MarkovTriple.Stochastic.Circle.circleKernel_continuous
#print axioms MarkovTriple.Stochastic.Circle.circle_isFeller
#print axioms MarkovTriple.Stochastic.Circle.circle_fellerKernel_eq
#print axioms MarkovTriple.Stochastic.Circle.circle_fellerKernel_eq'
#print axioms MarkovTriple.Stochastic.Circle.circleFellerBridge
#print axioms MarkovTriple.Stochastic.Circle.circleFellerBridge_κ
#print axioms MarkovTriple.Stochastic.Sphere.sphere_isFeller
#print axioms MarkovTriple.Stochastic.Sphere.sphereBridge
#print axioms MarkovTriple.Stochastic.Sphere.sphereBridge_isMarkov
