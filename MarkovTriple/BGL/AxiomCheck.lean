import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Frozen.FormDomain
import MarkovTriple.BGL.Frozen.Fisher
import MarkovTriple.BGL.FullBasic
import MarkovTriple.BGL.Consistency
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
