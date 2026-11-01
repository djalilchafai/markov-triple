# Divergences layer: port status

Prover/extractor output for Phase 1. CR = cutoff-rigidity-diffusions (`CutoffRigidity/`), GP = ginibre-poincare
(`GinibrePoincare/Analysis/`), CF = cutoff-fastdiff (`Cutfast/`). All files are in `MarkovTriple/Divergences/`,
namespace `MarkovTriple`, no `module` system, plain `import Mathlib`. All entries are fully proved (no sorry, no axiom,
no maxHeartbeats change); `AxiomCheck.lean` verifies that every declaration depends only on
propext / Classical.choice / Quot.sound.
Ported files have NOT been audited by a separate hostile auditor yet.

| Ported theorem / definition | Source | Status | Changes |
|---|---|---|---|
| `Ent` (def), `squareEntropy` (abbrev `Ent μ (f^2)`) | CR `Riemann/DiffTight.lean` `entL`; GP `GinibreEntropy.lean` `squareEntropy` | defined | ONE def: `Ent` already exists in `Frozen/Ent.lean` (identical body to `entL`) and is imported, not redefined; `squareEntropy_def` is `rfl` |
| `Ent_nonneg`, `squareEntropy_nonneg` | GP `squareEntropy_nonneg` | proved | generalized to `Ent` of nonneg function |
| `Ent_map`, `squareEntropy_map`, `Ent_eq_of_moments`, `squareEntropy_eq_of_moments` | GP `squareEntropy_map`, `_eq_of_moments` | proved | generalized to `Ent` |
| `klDiv_withDensity_eq_ofReal_integral` | CR `EntropyDissipation.lean` `klDiv_withDensity_eq_density_entropy` | proved | renamed only |
| `klDiv_withDensity_eq_ofReal_Ent` | new | proved | `Ent` form of the bridge |
| `klDiv_ne_top_iff_integrable_rnDeriv_mul_log`, `klDiv_eq_ofReal_Ent_rnDeriv`, `toReal_klDiv_eq_Ent_rnDeriv` | new (CR `LangevinDeBruijn.lean` has a related withDensity statement) | proved | bridge `klDiv ν μ = Ent μ (dν/dμ)` for probability measures |
| `totalVariationDistance` + `_nonneg/_le_one/_self/_map_le/_map_measurableEquiv`, `abs_measureReal_sub_le_..`, `_ge_mean_separation` | CR `TotalVariation.lean` | proved | namespace only. NOT ported: `totalVariationDistance_affineGaussian_lower` (needs CR Gaussian files) |
| `binaryDivergence_ge_two_mul_sq`, `klFun_set_average_le`, `binaryDivergence_le_klDiv_toReal`, `two_mul_sq_measureReal_sub_le_klDiv_toReal` | CR `Pinsker.lean` | proved | namespace only |
| `totalVariationDistance_sq_le_klDiv_toReal`, `totalVariationDistance_sq_le_klDiv` (Pinsker, TV normalized sup_A, `TV^2 <= KL/2`) | CR `Pinsker.lean` | proved | namespace only |
| `Ent_prod_decomposition`, `Ent_prod_tensorization`, `Ent_prod_tensorization_bounded` | GP `EntropyProductDecomposition`, `IntegralEntropyTensorization` | proved | generalized from `squareEntropy` to `Ent` of nonneg `h` (square versions are corollaries) |
| `squareEntropy_prod_tensorization`, `squareEntropy_prod_tensorization_bounded` | GP `IntegralEntropyTensorization` | proved | hypotheses unchanged (bounded version: `\|f\| <= C` kept, `0<=C` hypothesis dropped as unneeded) |
| `integral_entropy_matrix_tensorization(_nonneg)`, `mul_log_sub_mul_log_ge_sub`, `integrable_mul_log_fiberMoment`, `ae_zero_or_pos_fiberMoment`, `integrable_mul_log_of_bounded_nonneg` | GP `IntegralEntropyTensorization` | proved | verbatim |
| `entropyPhi`, `finite_log_sum`, `entropy_matrix_tensorization`, `uniformFiniteEntropy(_tensorization, _eq)`, `uniformFiniteLSI_tensorization` | GP `FiniteEntropyTensorization` | proved | verbatim |
| `Coupling`, `wassersteinSq` (W2^2, `ENNReal`), `wasserstein2` (= `wassersteinSq^(1/2)`), `productCoupling`, `Coupling.{diag,swap,map}` | CR `Transport.lean` `squaredWasserstein`, `Statements.lean`/`Challenge.lean` `wasserstein2`, `Riemann/TransportW2.lean` `cost2`, CF `Defs.lean` `wassersteinSq` | defined | FOUR defs merged. Base: CR `squaredWasserstein` (couplings = all measures with the marginals) on `PseudoEMetricSpace`. CF's variant ranges over probability couplings; equal for probability marginals (`wassersteinSq_eq_wassersteinSqP`), may differ for non-probability measures |
| `wasserstein2_sq_eq`, `wassersteinSq_le_cost`, `wasserstein2_le_cost`, `Coupling.isProbabilityMeasure` | CR `Transport`, `TransportW2` | proved | |
| `wassersteinSq_self`, `wassersteinSq_comm`, `wasserstein2_self/_comm` | CF `wassersteinSq_comm` (+ new) | proved | |
| `Coupling.eq_dirac_prod`, `wassersteinSq_dirac` | CR `Transport.lean` | proved | |
| `wassersteinSq_map_le`, `wasserstein2_map_le` | CR `squaredWasserstein_map_le`, `cost2_map_le` | proved | now over `PseudoEMetricSpace` + measurable Lipschitz map, includes `K=0`; needs probability marginals |
| `quadratic_transport_weak_duality` (+ `_norm`) | CR `TransportWeakDuality.lean` | proved | generalized from normed space to `PseudoMetricSpace` with cost `dist^2`; `_norm` is the original statement |
| `exists_compact_transport_coupling_of_dual_budget` (+ helpers) | CR `CompactTransportDuality.lean` | proved | `set_option maxHeartbeats 800000` was REMOVED, proof compiles at default |
| `wassersteinSq_le_of_compact_dual_budget` | new | proved | Kantorovich duality (strong direction) for `W2^2` on a compact metric space |
| `wassersteinSq_map_affine` (Lemma 2.1, optimality of positive affine maps) | CF `Wasserstein.lean` `wassersteinSq_map_affine'` | proved | stated for unified `wassersteinSq` via bridge; original kept as `Gelbrich.wassersteinSqP_map_affine'` |
| `wassersteinSq_elliptic` (Lemma 2.2, Gelbrich/Bures formula) | CF `Elliptic.lean` `wassersteinSq_elliptic'` | proved | same bridge; `E d` renamed `Eu d` |
| `klFun_exponential_young`, `klLogWitness*`, `relativeEntropyTest`, `relativeEntropyTest_le_klDiv`, `klDiv_le_of_bounded_measurable_tests` (Donsker-Varadhan type) | CR `KLScalarVariational`, `KLVariationalMeasure` | proved | namespace only |
| `varentropy`, `salez_reverse_pinsker`, `klDiv_toReal_le_varentropy_of_tv_le`, ... | CR `Varentropy.lean` | proved | namespace only |

## Not ported (remaining for Phase 1)

- Euclidean / Lipschitz Kantorovich duality: CR `EuclideanTransportDuality`, `EuclideanLipschitzTransportDuality`, `CompactLipschitzTransportDuality` (+ `EuclideanCompactClipping`, `TransportCouplingCompactness`, `TransportMoments`, `CompactLipschitzApproximation`).
- `RelativeLpDistance.lean` (chi^2, relative L^p distance): imports Langevin-specific files (`LangevinL1Density`, `EntropyL2Bound`); needs untangling. Hellinger (`HellingerL2Convergence`) likewise.
- `KLCompactVariational`, `KLWeakLowerSemicontinuity`, `Talagrand`-type consequences; GP `EntropyL2Closure`, `SquareEntropyLinearization`, `EntropyLimitStability`; Gaussian W2 in CR; CF `Radial`, `Sphere`, `Asymptotics` (the `ForMathlib/` side; `MarkovTriple/ForMathlib/` is empty).
- Triangle inequality for `W2` (needs gluing lemma; not in any source repo as a standalone result).
- Rewriting the three projects as thin wrappers (Phase 1 second bullet) not started.
