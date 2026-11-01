import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Frozen.FormDomain
import MarkovTriple.BGL.Frozen.Fisher
import MarkovTriple.BGL.FullBasic
import MarkovTriple.BGL.Consistency
import MarkovTriple.BGL.Calculus.Identities
import MarkovTriple.BGL.Semigroup.Markov
import MarkovTriple.BGL.Semigroup.Conservative
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Semigroup.Characterization
import MarkovTriple.BGL.Calculus.Density
import MarkovTriple.BGL.Calculus.LSIExtend
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Sanity.Trivial
import MarkovTriple.BGL.Sanity.Circle

/-! Axiom audit of the BGL layer (build log must show only `propext`, `Classical.choice`,
`Quot.sound`). -/

#print axioms MarkovTriple.BGL.DiffusionTriple.semigroup
#print axioms MarkovTriple.BGL.DiffusionTriple.generator
#print axioms MarkovTriple.BGL.DiffusionTriple.exists_bound_D4
#print axioms MarkovTriple.BGL.DiffusionTriple.L_mul_ae
#print axioms MarkovTriple.BGL.DiffusionTriple.ΓA_ae_eq
#print axioms MarkovTriple.BGL.FullTriple.integrable_F7
#print axioms MarkovTriple.BGL.Sanity.trivialCompact
#print axioms MarkovTriple.BGL.Sanity.trivialCompact_CD
#print axioms MarkovTriple.BGL.Sanity.trivialCompact_PI
#print axioms MarkovTriple.BGL.Sanity.trivialCompact_LS
#print axioms MarkovTriple.BGL.Sanity.circleDiffusion

-- L1: fundamental identity, chain rule, positivity, sub-Markov
#print axioms MarkovTriple.BGL.DiffusionTriple.fundamental_identity
#print axioms MarkovTriple.BGL.DiffusionTriple.chain_rule_L
#print axioms MarkovTriple.BGL.DiffusionTriple.isMarkovianForm
#print axioms MarkovTriple.BGL.DiffusionTriple.semigroup_nonneg
#print axioms MarkovTriple.BGL.DiffusionTriple.isClipForm
#print axioms MarkovTriple.BGL.DiffusionTriple.semigroup_le_one
-- S11: independence of the exhaustion sequence, P_t 1 = 1, mass conservation
#print axioms MarkovTriple.BGL.DiffusionTriple.comparison
#print axioms MarkovTriple.BGL.DiffusionTriple.conservative_transfer
#print axioms MarkovTriple.BGL.DiffusionTriple.exists_nonneg_exhaustion
#print axioms MarkovTriple.BGL.StandardTriple.conservative_all
#print axioms MarkovTriple.BGL.DiffusionTriple.conservative_iff_semigroup_one
#print axioms MarkovTriple.BGL.DiffusionTriple.integral_semigroup_of_one
#print axioms MarkovTriple.BGL.StandardTriple.integral_semigroup
-- M1/S10: characterisation of the generator, second form of ergodicity
#print axioms MarkovTriple.BGL.DiffusionTriple.generator_iff_form
#print axioms MarkovTriple.BGL.DiffusionTriple.ergodic_iff_energy
#print axioms MarkovTriple.BGL.StandardTriple.energy_zero_const
-- M2: density of A₀ in D(E), Poincaré extension, entropy integrability
#print axioms MarkovTriple.BGL.DiffusionTriple.formDomain_approx
#print axioms MarkovTriple.BGL.DiffusionTriple.PI.extend
#print axioms MarkovTriple.BGL.DiffusionTriple.integrable_sq_mul_log_sq
#print axioms MarkovTriple.BGL.DiffusionTriple.LS.extend
-- ESA automatic for compact triples
#print axioms MarkovTriple.BGL.DiffusionTriple.core_of_invariant
#print axioms MarkovTriple.BGL.CompactTriple.esa_auto
