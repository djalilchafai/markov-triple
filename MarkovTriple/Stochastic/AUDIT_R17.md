# Round 17, Stream E: stochastic layer (self-audit, hostile reading) -- `STATEMENTS_R17.md`

New modules (all 0 warnings / 0 errors, no `sorry`, no `set_option`): `FellerMeasurable.lean`, `FellerProcessBridge.lean`,
`ExactCK.lean`, `AxiomCheckR17.lean` (all 19 declarations print only `propext, Classical.choice, Quot.sound`).
Nothing frozen/fenced was edited; `STATEMENTS_R17.md` is a `proposed` entry in `frozen-manifest.json`.

## What is proved

### (ii) Joint time-measurability, `MarkovProcessBridge` (priority 1) -- `FellerMeasurable.lean`, `FellerProcessBridge.lean`
* `isClosed_fellerOp_ball`: `{t | ‖P_t f - g‖_sup <= r}` closed.  Ingredients: `continuous_semigroup_apply` (BGL strong `L^2`
  continuity), `OrderClosedTopology (Lp ..)`, `clsC_le_iff` (full support: `[h_1] <= [h_2] <=> h_1 <= h_2` pointwise).
* `measurable_fellerOp_time`: `t |-> fellerOp hF t f` is Borel into `(C(X), sup)` (separable metric space: open set = countable union of
  closed balls with dense-sequence centres and rational radii).
* `measurable_fellerOp_joint`, `fellerKernel_measurable_joint`: `(t,x) |-> fellerKernel hF t x` jointly measurable
  (evaluation `C(X) x X -> R` continuous; `measurable_of_integrals_param` = R15 closed-set argument on an arbitrary parameter space).
* `fellerMarkovProcessData`, `fellerMarkovProcessBridge hF hcons : MarkovProcessBridge T` for EVERY conservative Feller triple
  on a compact metrizable space with full-support finite `mu` (kernels = `fellerKernel hF`, by `rfl`);
  `Sphere.sphereMarkovProcessBridge` (the zonal `S^3`, whose kernels are abstract: no formula, joint measurability was NOT available before).
  The circle and OU already had `MarkovProcessBridge`s by explicit formula (R15).

### (i) Feller-free exact CK (priority 2, PARTIAL) -- `ExactCK.lean`
* `ae_measure_eq_of_forall`, `KernelRepresentation.kappa_zero_ae` (`kappa_0 = delta_x` a.e.),
* `KernelRepresentation.exists_exact_ck` (countably generated, finite `mu`, `mu.bind kappa_t <= mu`): for every COUNTABLE `S ⊆ R>=0`
  there is a measurable conull properly exceptional `G` (`kappa_s(x,G^c) = 0` for `x in G`, `s in S`) on which
  `kappa_{s+t}(x,.) = (kappa_t o_k kappa_s)(x,.)` for ALL `s,t in S` and `kappa_0(x,.) = delta_x`;
  `rieszKernel_exists_exact_ck`: the instance for the Riesz kernels of every triple on a compact metrizable space (S = rationals is the typical use).
  This is the discrete-time Fukushima regularisation.  Sub-invariance (BGL symmetry, R15) is exactly what makes `G` properly exceptional.

## NOT proved (no overclaim)
1. **No exact kernel semigroup for all real times without Feller.**  `exists_exact_ck` is for a countable set of times only; passing to
   real `t` needs pathwise right-continuity (Kuznetsov / right-process theory or a Feller-type regularity of `P_t`), which `L^2` strong
   continuity does not give.  Consequently there is no `KernelBridge` / `MarkovProcessBridge` from the plain Riesz kernels, and none is claimed.
   The map `x |-> kappa_t(x,.)` of the Riesz kernels is chosen separately for each `t`, so no joint measurability is claimed for it either:
   (ii) holds for the Feller kernels only.  Regular-conditional-probability / standard-Borel versions: BGL does not use them (it assumes
   the kernel/density representation or constructs it from the Feller/Hunt regularity); not formalised, and nothing is said about them.
2. `exists_exact_ck` gives measures on `E`; it does not repackage the restricted kernels as a `SubMarkovKernelSemigroup` on the subtype `G`
   with time monoid `S` (not needed for the statement; bookkeeping only).
3. **(iii) Non-compact extension** (locally compact sigma-compact Polish `X`, `C_0`/`C_c` test classes): NOT attempted as a theorem.  Precisely what remains:
   (a) `C_c(X)` replaces `C(X)`: the countable Z-span `V` must be dense in `C_c` for the inductive-limit topology and contain a cut-off
   sequence `chi_n` (`chi_n = 1` on `K_n`), with a.e. bounds `|F v| <= ||v|| F chi_n` and `F chi_n <= 1` (the latter from `semigroup_le_one`, as `1 not in L^2`);
   (b) the Riesz-Hahn-Banach extension `exists_posFunctional` must be redone on each `C_{K_n}` (sup-norm closed subspaces of functions supported in `K_n`),
   compatibly in `n`, using the majorant `||f|| chi_n`; (c) Mathlib's `RealRMK` (positive functionals on `C_c`) gives the Radon kernels;
   (d) `kernelRep_of_dense` with `C_c` dense in `L^2(mu)` (Radon `mu`); sub-invariance via inner regularity.  Alternative reduction
   (also not done): a strictly positive `h = R_1 g` with `P_t h <= e^t h`, the weighted isometry `L^2(h^2 mu) -> L^2(mu)` and the one-point compactification.
   Each is a long but standard argument; none is stated as an assumption anywhere.
4. Feller property is still an explicit hypothesis (not automatic).

## Hostile self-audit
* Faithfulness: `measurable_fellerOp_time` target is `C(X,R)` with Mathlib's `ContinuousMap.measurableSpace` (= Borel of the compact-open/sup topology),
  so the statement is not vacuous; `fellerMarkovProcessBridge` is a structure with all five fields of the mirror plus `rep`, `invariant` (checked: `rfl` to the R16 kernels).
* No vacuous hypotheses: `IsFeller`, full support, conservativity are exactly the R16 hypotheses, discharged for the circle and zonal `S^3` (R16),
  so `sphereMarkovProcessBridge` is a genuine instance.  `exists_exact_ck`: `hbind` is proved (not assumed) for the Riesz kernels; `S` countable is needed for the proof
  (countable intersections of conull sets); the case `S = R>=0` is not claimed.
* Edge cases: `S = {}` gives a trivial `G` (conull; fine); `0 not in S` leaves `kappa_0` unconstrained (the last clause is an implication).
* Mirror caveat inherited: `MarkovProcessSemigroupData` mirrors Armstrong's structure field by field (read as text only; never imported).
* The name `kernel` (not `kappa`) is the field of `MarkovProcessBridge`; see erratum R17-1.
* Axioms: `AxiomCheckR17.lean`, standard only.
