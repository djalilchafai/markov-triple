# Round 16 self-attack (Armstrong step (b)), against `STATEMENTS_R16.md`

"Checked" = by a Lean statement or reading the final code.

## A. What is proved (and its exact hypotheses)
1. `fellerBridge hF hcons : KernelBridge T` needs: `X` compact Hausdorff second countable Borel; `T.μ` finite;
   (S) `T.μ.IsOpenPosMeasure`; (F) `IsFeller T`; (C) `P_t 1 = 1`.  Conclusion: kernels defined at EVERY `x` with exact CK
   (`fellerKernel_add`), `κ_0 = id` (`fellerKernel_zero`), Markov (`fellerKernel_isMarkov`), `μ.bind κ_t = μ`
   (`fellerKernel_bind`), `rep` for bounded measurable `L²` (`fellerKernel_rep`, via `kernelRep_of_dense`).
2. Without (C) one still gets `fellerSemigroup : SubMarkovKernelSemigroup X` + sub-invariance `≤` + `rep`, but NOT a
   `KernelBridge` (its `invariant` field is an EQUALITY, false with killing).  Checked: no claim made.
3. (C) is automatic for `StandardTriple` with finite `μ` (`standardSemigroup_one_fin`, from S11 + `conservative_all`).

## B. Attacks on the hypotheses
4. (S) vacuity/necessity: without full support a.e.-equal continuous functions need not coincide, the continuous
   representative `fellerOp` is not determined, linearity/CK would only hold on `supp μ`; we do not restrict to the support.
   Instances: circle (Haar `IsAddHaarMeasure ⇒ IsOpenPosMeasure`), sphere (`μZ`, proved by hand in `SphereFeller.lean`,
   pulling back to `θ`-space; uses `closure (Ioo 0 π) = Icc 0 π`).  Checked in Lean.
5. (F) is a compatibility between `P_t` and the topology of `X`, not between `Γ, L` and `X`: the triple has no topology.
   It is NOT automatic (a Markov semigroup with discontinuous drift or an indicator-type kernel violates it); no Lean
   counterexample is given.  It is proved for the circle (`circle_isFeller`, from the explicit wrapped Gaussian,
   dominated convergence) and for the zonal `S³` (`sphere_isFeller`: `semigroup_cls_mem` = smoothing of `P_t` on the
   dense subalgebra `AC` + `isFeller_of_dense`).  The sphere `P_t 1 = 1` is `Sphere.semigroup_one`.
6. Consistency (non-triviality of the result): `circle_fellerKernel_eq` shows the abstract Riesz-Markov-Feller kernels
   of the circle EQUAL the wrapped Gaussian `circleKernel` at every point; so `fellerKernel` is non-trivial (not a Dirac or
   zero junk kernel) and the identification is everywhere, not a.e.  `fellerKernel_unique` gives the general uniqueness
   (weakly continuous in `x` + represents `P_t` a.e. on `C(X)` ⇒ equal everywhere), used for this link.

## C. Representatives, null sets, junk
7. a.e. vs everywhere: all a.e. identities of `P_t` (linearity, positivity, `|P_t f| ≤ ‖f‖`, `P_0 = id`, `P_{s+t} = P_sP_t`)
   are converted to everywhere identities between continuous functions by (S) (`Continuous.ae_eq_iff_eq`,
   `cont_bound_of_ae`, `cont_nonneg_of_ae`, `clsC_injective`).  Hence the junk values of Riesz at null sets of `x` are gone.
   `rep` itself stays a.e. (inherent: `P_t` is an `L²` class).  `fellerKernel` agrees `μ`-a.e. with the R15 `rieszKernel`
   (by `KernelRepresentation.ae_unique`); this is not stated as a Lean theorem.
8. `t = 0` junk: `fellerOp 0 f = f` from `semigroup_zero` and injectivity, so `κ_0(x,·) = δ_x` exactly (RMK uniqueness
   via `measure_ext_C`, `ext_of_forall_integral_eq_of_IsFiniteMeasure`).
9. Time measurability: `KernelBridge` needs none.  The map `(t,x) ↦ κ_t(x,·)` is NOT proved jointly measurable
   (Feller + L²-strong continuity give only separate-in-`x` continuity; pointwise measurability in `t` needs sup-norm strong
   continuity, not available abstractly).  So no `MarkovProcessBridge` for `fellerKernel` is claimed; for OU the R15
   joint measurability was by explicit formula.

## D. Routes not taken (decision)
10. Route B (no Feller, rational times): the a.e. CK for countably many pairs gives an exact CK on a conull set
    `G` after shrinking to `G_∞ = ⋂ G_n` with `κ_s(x, G^c) = 0` (properly exceptional set, Fukushima), for dyadic times
    only; passing to real `t` needs right-continuity of paths in `t` (pathwise), which does not follow from strong
    continuity in `L²`.  So no `KernelBridge` (which asks for ALL real `s,t` and ALL `x`) can be obtained this way by
    textbook arguments.  NOT formalised, NOT claimed.
11. Non-compact (σ-finite, locally compact, second countable) extension: would need `C_0`-Feller, `C_c` dense in `L²(μ)`
    (Radon), Riesz-Markov on `C_c` (Mathlib has it), cut-offs for the bound and sub-probability kernels; open, not attempted
    (R15 audit item 10 still stands).

## E. Hygiene
12. `set_option linter.unusedSectionVars false` in the new files only (generic section variables).
13. Axioms: all 30 new declarations in `AxiomCheckR16.lean` print only `propext, Classical.choice, Quot.sound`.

## F. Attack surface (for the hostile auditor)
* Is `IsFeller` (a.e. form with `clsC`) really the right "Feller" notion (vs. `P_t C(X) ⊂ C(X)` literally)?  Both agree when (S) holds.
* `clsC_injective` and `fellerOp_add_time` (order of `semigroup_add`): re-read `DiffusionTriple.semigroup_add`.
* `fellerKernel` measurability via `measurable_of_integrals` (R15) for the family `x ↦ fellerMeasure t x` defined by choice.
* `fellerKernel_bind` uses `Kernel.integral_comp` with `Kernel.const Unit`: check the identification with `Measure.bind`.
* SphereFeller `IsOpenPosMeasure μZ`: the open-set argument; `sT.μ` vs `μZ` instance transfer by `inferInstanceAs`.
* Circle: the instance `IsOpenPosMeasure cT.μ` transferred from Haar; `circle_rep_full` applied to continuous `f` (bounded, measurable).
* Whether `KernelBridge`'s equality `invariant` is too strong for the sub-Markov case (design of R15, unchanged).
* The "full fix" is conditional on (F)+(S) and on compactness: the unconditional general statement is NOT proved.
