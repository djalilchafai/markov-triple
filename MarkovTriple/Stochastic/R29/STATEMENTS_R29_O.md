# Round 29, Stream O (stochastic layer): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R29`.  Goal: close as many as possible of the instances listed WITHOUT a
`MarkovProcessBridge` in GAPS "Round 28, Stream M" (survey table).  Each item is a statement; whatever is not delivered is reported in the
Status section (to be appended) and in GAPS, not silently dropped.

## O1. `lebesgueFull` (the 1-d Lebesgue `FullTriple` on `R`) -- file `R29/Lebesgue1.lean`
Route: port of R25 (`lebesgueRd_isFellerC0`, `heatKernelRd`) to the 1-d heat operator `heatM` of `Instances/Lebesgue/Heat.lean`.
```
theorem lebesgue_isFellerC0 : R24.IsFellerC0 lebesgueFull.toDiffusionTriple
noncomputable def heatKernel1 (t : R>=0) : Kernel R R                      -- x |-> gaussianReal x (2 t)
theorem fellerKernelInf_lebesgue (t : R>=0) (x : R) :
    R24.fellerKernelInf lebesgue_isFellerC0 t x = gaussianReal x (2 * t)    -- as NNReal variance `2 * t`
theorem lebesgue_hM (t) (x) : R24.fellerKernelInf lebesgue_isFellerC0 t x Set.univ = 1
noncomputable def lebesgueFull_bridge : MarkovProcessBridge lebesgueFull.toDiffusionTriple
theorem lebesgueFull_bridge_kernel (t) (x) : lebesgueFull_bridge.kernel t x = gaussianReal x (2 * t)
```

## O2. The open zonal sphere `oStandard`, `oFull` (`(-1,1)`, `S^3`, Gegenbauer lambda = 1) -- file `R29/OpenSphere.lean`
`mu_Z = (2/pi) sin^2 theta` pushed by `cos` (Chebyshev-U weight `sqrt(1-x^2)`), eigenvalues `k (k+2)`, `|U_k| <= k+1`.  Route: for `t > 0` the Feller kernels
`fellerKernel sphere_isFeller t x` of the compact zonal sphere satisfy `|int f d kappa_t(x,.)| <= C_t ||f||_{L^2(mu_Z)}` at EVERY `x` (spectral
series, `C_t = sum_k e^{-tk}(k+1)`), hence `kappa_t(x,.) << mu_Z` at every `x` and the poles `{+-1}` are `kappa_t(x,.)`-null; exact Chapman-Kolmogorov
on `(-1,1)` and exact `kappa_0 = id` then pass to the open subtype.
```
theorem sphere_pole_null (t : R>=0) (ht : 0 < t) (x : Zon) (A : Set Zon) (hA : MeasurableSet A) (h : mu_Z A = 0) :
    fellerKernel sphere_isFeller t x A = 0
theorem sphere_kernel_pole_null (t : R>=0) (ht : 0 < t) (x : Zon) : fellerKernel sphere_isFeller t x ZonOSet^c = 0
noncomputable def oMarkovProcessBridge : MarkovProcessBridge oT                       -- kernels = restriction of the Feller kernels to (-1,1)
noncomputable def oStandard_bridge : MarkovProcessBridge oStandard.toDiffusionTriple
noncomputable def oFull_bridge : MarkovProcessBridge oFull.toDiffusionTriple
theorem oMarkovProcessBridge_kernel (t) (x : ZonO) (A : Set ZonO) (hA : MeasurableSet A) :
    oMarkovProcessBridge.kernel t x A = fellerKernel sphere_isFeller t (jO x) (jO '' A)
theorem oMarkovProcessBridge_isMarkov : forall t x, oMarkovProcessBridge.kernel t x univ = 1
```

## O3. `gaussRdFull d` (`R^d`, standard Gaussian, `FullTriple`) -- file `R29/GaussRd.lean`
Target (attempted; reported in Status whether delivered):
```
noncomputable def mehlerKernelRd (d) (t : R>=0) : Kernel (Fin d -> R) (Fin d -> R)      -- x |-> Measure.pi (fun i => gaussianReal (e^{-t} x_i) (1 - e^{-2t}))
theorem mehlerKernelRd_zero : mehlerKernelRd d 0 = Kernel.id
theorem mehlerKernelRd_add (s t) : mehlerKernelRd d (s + t) = (mehlerKernelRd d t).comp (mehlerKernelRd d s)    -- exact CK
theorem mehlerKernelRd_invariant (t) : (gam d).bind (mehlerKernelRd d t) = gam d
noncomputable def gaussRdFull_bridge (d : N) : MarkovProcessBridge (gaussRdFull d).toDiffusionTriple
```
The first four are the unconditional product-Mehler statements; `gaussRdFull_bridge` needs the identification of the Friedrichs semigroup of
`gaussRdFull d` with the Mehler semigroup (`rep`), which is the hard part.

## O4. Gibbs and Riemannian instances (`gibbs*`, `riem*`) -- conditional bridges + exact list of missing hypotheses (file `R29/Conditional.lean`)
For `G.gibbsFull_unconditional` (`R`, `mu = e^{-V}dx`), `G.gibbsRdFull_unconditional`, `E.fullU` (`Rd d`, elliptic data) and `riemFull_unconditional`
(`Rd d`): the R27 theorem `fellerMarkovProcessBridgeInf_of_ac_init` needs (a) `IsFellerC0`, (b) `IsFiniteMeasureOnCompacts` and `IsOpenPosMeasure` of the
reference measure, (c) `hac` (kernels a.c. w.r.t. `mu` for `t > 0`), (d) `hinit` (pointwise initial condition on `C_c`).  Delivered, for each instance whose
reference measure satisfies (b) (proved, not assumed, where the weight is strictly positive and locally bounded):
```
noncomputable def gibbsFull_bridge_of_feller (hF : IsFellerC0 G.gibbsFull_unconditional.toDiffusionTriple) (hac) (hinit) :
    MarkovProcessBridge G.gibbsFull_unconditional.toDiffusionTriple
(and the analogous `gibbsRdFull_bridge_of_feller`, `fullU_bridge_of_feller`, `riemFull_bridge_of_feller`, when (b) is available)
```
These are specialisations of the R27 theorem, NOT unconditional bridges: (a), (c), (d) are not established in the library for non-Gaussian `V`
or non-constant elliptic data and are recorded as the missing hypotheses in GAPS.

## Status (appended after the proofs; hash re-registered for this file only)
* O1 DELIVERED as frozen (`R29/Lebesgue1.lean`): `lebesgue_isFellerC0`, `heatKernel1`, `fellerKernelInf_lebesgue`, `lebesgue_hM`, `lebesgueFull_bridge`, `lebesgueFull_bridge_kernel` (plus `heatKernel1_add`, `heatKernel1_bind`).
* O2 DELIVERED as frozen (`R29/PoleNull.lean`, `R29/OpenSphere.lean`): `sphere_pole_null`, `sphere_kernel_pole_null`, `oMarkovProcessBridge`, `oStandard_bridge`, `oFull_bridge`, `oMarkovProcessBridge_kernel`, `oMarkovProcessBridge_isMarkov`; extra `smoothing_sup`, `sphere_kernel_bound`, `sphere_kernel_compact_null`, `sphere_kernel_ac`.
* O3 PARTIAL (`R29/GaussRd.lean`): `mehlerKernelRd`, `_zero`, `_add`, the invariance theorem under the name `mehlerKernelRd_bind` (frozen name `mehlerKernelRd_invariant`), `_apply_pi`, `_measurable_joint`; the frozen UNCONDITIONAL `gaussRdFull_bridge` is NOT proved, only `gaussRdFull_bridge_of_rep` (ERRATA R29-O-1).
* O4 DELIVERED as frozen (`R29/Conditional.lean`): the four `*_bridge_of_feller` and the measure instances; unconditional bridges are NOT obtained (ERRATA R29-O-4).
