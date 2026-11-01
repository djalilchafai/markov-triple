import Mathlib
import MarkovTriple.Hilbert.Complexify
import MarkovTriple.Hilbert.Friedrichs
import MarkovTriple.Hilbert.CfcSemigroup
import MarkovTriple.Hilbert.SemigroupDeriv
import MarkovTriple.Hilbert.SemigroupSmoothing
import MarkovTriple.Hilbert.Resolvent
import MarkovTriple.Hilbert.ResolventGenerator
import MarkovTriple.Hilbert.Generator
import MarkovTriple.Hilbert.SpectralGap
import MarkovTriple.Hilbert.Existence
import MarkovTriple.Hilbert.BeurlingDeny
import MarkovTriple.Hilbert.DirMerge
import MarkovTriple.Hilbert.DirBridge
import MarkovTriple.Hilbert.TripleForm
import MarkovTriple.Hilbert.Bridge
import MarkovTriple.Hilbert.Closure
import MarkovTriple.Hilbert.MarkovCriterion
import MarkovTriple.Hilbert.OperatorSquareCompletion
import MarkovTriple.Hilbert.Sanity

/-!
# Axiom audit of `MarkovTriple.Hilbert`

Explicit `#print axioms` for the main public theorems; each must list only
`propext`, `Classical.choice`, `Quot.sound`.
-/

open MarkovTriple.Hilbert

-- Friedrichs / resolvent / semigroup
#print axioms FormData.R_unitOp
#print axioms FormData.E_resolvent
#print axioms FormData.semigroup_mapsTo
#print axioms cfcSemigroup_eigen
#print axioms tendsto_eulerOp
#print axioms FormData.hasRightDeriv_semigroup_of_mem_range
-- generator
#print axioms resolventGenerator_selfAdjoint
#print axioms FormData.generator_selfAdjoint
#print axioms FormData.generator_extends
#print axioms FormData.tendsto_generator_iff
-- (1) existence
#print axioms FormData.exists_semigroup
-- (2) spectral gap <-> L2 decay
#print axioms FormData.hasExpDecay_of_hasSpectralGap
#print axioms FormData.hasSpectralGap_of_hasExpDecay
#print axioms FormData.hasSpectralGap_iff_hasExpDecay
-- Beurling-Deny
#print axioms FormData.semigroup_mapsTo_of_contraction
-- merge of the two copies
#print axioms FormData.dirFriedrichs
#print axioms FormData.exists_contraction_of_approx
#print axioms DirFriedrichs.closed_of_bounded
-- triple
#print axioms formData
#print axioms inner_formA
-- (3) bridge
#print axioms tripleSemigroup_one
#print axioms tripleSemigroup_nonneg
#print axioms isSemigroupOf_tripleSemigroup
#print axioms isMarkovianForm_of_approx
#print axioms FullMarkovTriple.generator_graph_eq_closure
#print axioms trivialTriple_friedrichs_isSemigroupOf
#print axioms OperatorSquareCompletion.integratedGammaTwo_of_poincare
