import Mathlib
import MarkovTriple.Divergences.Entropy
import MarkovTriple.Divergences.TotalVariation
import MarkovTriple.Divergences.Pinsker
import MarkovTriple.Divergences.Tensorization
import MarkovTriple.Divergences.Wasserstein
import MarkovTriple.Divergences.WeakDuality
import MarkovTriple.Divergences.CompactDuality
import MarkovTriple.Divergences.Gelbrich
import MarkovTriple.Divergences.KLScalarVariational
import MarkovTriple.Divergences.KLVariational
import MarkovTriple.Divergences.Varentropy

/-!
# Axiom audit of `MarkovTriple.Divergences`

Explicit `#print axioms` for the main public theorems of `MarkovTriple.Divergences`; each must
list only `propext`, `Classical.choice`, `Quot.sound`.
-/

open MarkovTriple

#print axioms Ent_nonneg
#print axioms squareEntropy_nonneg
#print axioms Ent_map
#print axioms Ent_eq_of_moments
#print axioms klDiv_withDensity_eq_ofReal_integral
#print axioms klDiv_withDensity_eq_ofReal_Ent
#print axioms klDiv_ne_top_iff_integrable_rnDeriv_mul_log
#print axioms klDiv_eq_ofReal_Ent_rnDeriv
#print axioms toReal_klDiv_eq_Ent_rnDeriv
#print axioms totalVariationDistance_le_one
#print axioms totalVariationDistance_map_le
#print axioms totalVariationDistance_map_measurableEquiv
#print axioms totalVariationDistance_ge_mean_separation
#print axioms binaryDivergence_ge_two_mul_sq
#print axioms two_mul_sq_measureReal_sub_le_klDiv_toReal
#print axioms totalVariationDistance_sq_le_klDiv_toReal
#print axioms totalVariationDistance_sq_le_klDiv
#print axioms Ent_prod_decomposition
#print axioms Ent_prod_tensorization
#print axioms Ent_prod_tensorization_bounded
#print axioms squareEntropy_prod_tensorization
#print axioms squareEntropy_prod_tensorization_bounded
#print axioms integral_entropy_matrix_tensorization_nonneg
#print axioms entropy_matrix_tensorization
#print axioms uniformFiniteEntropy_tensorization
#print axioms uniformFiniteLSI_tensorization
#print axioms wasserstein2_sq_eq
#print axioms wassersteinSq_self
#print axioms wassersteinSq_comm
#print axioms wassersteinSq_dirac
#print axioms wassersteinSq_map_le
#print axioms wasserstein2_map_le
#print axioms quadratic_transport_weak_duality
#print axioms quadratic_transport_weak_duality_norm
#print axioms exists_compact_transport_coupling_of_dual_budget
#print axioms wassersteinSq_le_of_compact_dual_budget
#print axioms wassersteinSq_map_affine
#print axioms wassersteinSq_elliptic
#print axioms klFun_exponential_young
#print axioms relativeEntropyTest_le_klDiv
#print axioms klDiv_le_of_bounded_measurable_tests
#print axioms klDiv_toReal_le_varentropy_of_tv_le
#print axioms salez_reverse_pinsker
#print axioms wasserstein2_comm
#print axioms Coupling.eq_dirac_prod
