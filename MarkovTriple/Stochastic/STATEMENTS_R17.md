# Round 17 (stochastic layer, Stream E): frozen target statements

Written BEFORE any proof (Armstrong method).  Later changes only by a logged erratum in `ERRATA.md` (prefix `R17-`).
Namespace `MarkovTriple.Stochastic`.  Existing files are untouched.  Textbook source throughout: BGL Sect. 1.2-1.4
(Markov semigroup, kernel/density representation `P_t f(x) = int f dp_t(x,.)`, Chapman-Kolmogorov, `mu`-invariance,
Riesz-Markov representation of a positive contraction); the cited measure theory is standard (Mathlib).
Standing setting of (A): `X` compact Hausdorff second countable Borel, `T : DiffusionTriple X`, `[IsFiniteMeasure T.mu]`,
`[T.mu.IsOpenPosMeasure]`, `hF : IsFeller T` (R16).

## (A) Priority (ii): joint time-measurability and `MarkovProcessBridge` for the Feller kernels  (`FellerMeasurable.lean`)

```
lemma measurable_of_integrals_param {Y} [MeasurableSpace Y] {kappa : Y -> Measure X} [forall y, IsFiniteMeasure (kappa y)]
    (h : forall f : C(X,R), Measurable fun y => int z, f z d(kappa y)) : Measurable kappa
lemma isClosed_fellerOp_ball (f g : C(X,R)) (r : R) :
    IsClosed {t : R>=0 | forall x, |fellerOp hF t f x - g x| <= r}                 -- L^2-strong continuity + order-closedness of L^2
theorem measurable_fellerOp_time (f : C(X,R)) : Measurable fun t : R>=0 => fellerOp hF t f   -- into (C(X,R), sup norm), Borel
theorem measurable_fellerOp_joint (f : C(X,R)) : Measurable fun p : R>=0 x X => fellerOp hF p.1 f p.2
theorem fellerKernel_measurable_joint : Measurable fun p : R>=0 x X => fellerKernel hF p.1 p.2
noncomputable def fellerMarkovProcessData : MarkovProcessSemigroupData X     -- sub-Markov; fields are those of fellerSemigroup
noncomputable def fellerMarkovProcessBridge (hcons : forall t, T.semigroup t T.one2 = T.one2) : MarkovProcessBridge T
theorem fellerMarkovProcessBridge_toKernelBridge_kappa : (fellerMarkovProcessBridge hF hcons).kappa = fellerKernel hF   -- rfl
```
Mathematical content: for `f in C(X)`, `t |-> P_t [f]` is `L^2`-continuous (`continuous_semigroup_apply`), and
`{u : |u - [g]| <= r a.e.}` is closed in `L^2` (`OrderClosedTopology (Lp ..)`); with full support, for continuous `h`,
`||h - g||_sup <= r  <=>  |h - g| <= r a.e.`, so `t |-> ||fellerOp t f - g||_sup` has closed sublevel sets (lower
semicontinuous), hence `t |-> fellerOp t f in C(X)` is Borel measurable (separable metric target); evaluation
`C(X) x X -> R` is continuous.  Closed-set approximation (as in R15 `measurable_of_integrals`) gives the kernel.

File `FellerProcessBridge.lean`:
```
noncomputable def sphereMarkovProcessBridge : MarkovProcessBridge Sphere.sT          -- the zonal S^3 (R16 `sphereBridge`)
theorem sphereMarkovProcessBridge_kappa : sphereMarkovProcessBridge.kappa = (sphereBridge).kappa
```
NOT claimed: joint measurability for the (non-Feller) Riesz kernels of R15 (`rieszKernel` is chosen separately for each `t` by
choice; no relation between different `t`, so no measurability in `t` can be proved for them).

## (B) Priority (i): Feller-free exact Chapman-Kolmogorov on a conull set, for countably many times  (`ExactCK.lean`)

Setting: `E` measurable, `CountablyGenerated`, `T : DiffusionTriple E`, `[IsFiniteMeasure T.mu]`, `K : KernelRepresentation T`,
`hbind : forall t, T.mu.bind (K.kappa t) <= T.mu` (sub-invariance; proved for the Riesz kernels, `rieszKernel_subInvariant`).
```
theorem KernelRepresentation.kappa_zero_ae : forall^m x dT.mu, K.kappa 0 x = Measure.dirac x
theorem KernelRepresentation.exists_exact_ck (S : Set R>=0) (hS : S.Countable) (hbind) :
  exists G : Set E, MeasurableSet G /\ T.mu Gc = 0 /\
    (forall x in G, forall s in S, K.kappa s x Gc = 0) /\                                   -- G is "properly exceptional"
    (forall x in G, forall s in S, forall t in S, K.kappa (s+t) x = (K.kappa t o_k K.kappa s) x) /\   -- EXACT CK on G, pairs from S
    (0 in S -> forall x in G, K.kappa 0 x = Measure.dirac x)
```
(Fukushima-type / "Route B" of R16.)  Corollary for the Riesz kernels of a triple on a compact metrizable space:
```
theorem rieszKernel_exists_exact_ck (T : DiffusionTriple X) [IsFiniteMeasure T.mu] (S : Set R>=0) (hS : S.Countable) : <the above for rieszKernelRep T>
```
Sharpness (NOT claimed): extension from `S` countable to all real `t` (needs path regularity); this is exactly what the Feller
property of R16 provides.  `S = {rational times}` is the intended instance.

## (C) Priority (iii): non-compact extension

Not attempted as a theorem; the precise remaining work is listed in `AUDIT_R17.md` (section "Not proved").
