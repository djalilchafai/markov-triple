# Round 28, Stream M (stochastic layer): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R28`.  Goal: close the R27 open item "Markov kernels / bridge for `goFullTriple`"
(Gegenbauer `lambda = 3/2`, `goFullTriple : FullTriple R`, `goMu = (3/4)(1-x^2)dx` on `(-1,1)`, zero off `[-1,1]`).

Obstruction recalled (R27 `goMu_not_isOpenPos`): `goMu` is not of full support on `X = R`, so R24 `fellerKernelInf` (which needs
`IsOpenPosMeasure`) cannot be applied on `R`.  Route: restrict to the compact subtype `GI := Set.Icc (-1) 1`, where `goMuI := goMu.comap Subtype.val`
has full support, transport the *semigroup* (not the whole `DiffusionTriple`) by the restriction isometry, run the compact Feller kernel construction
(R16, abstracted from `DiffusionTriple X` to the semigroup data it uses), and push the kernels back to `R` along the clamp retraction.

## M1. Compact transport (files `R28/Transport.lean`, `R28/GoCompact.lean`)
```
abbrev GI : Type := Set.Icc (-1 : R) 1
noncomputable abbrev goMuI : Measure GI := goMu.comap Subtype.val
instance : IsProbabilityMeasure goMuI
instance : goMuI.IsOpenPosMeasure
noncomputable def goRestr : Lp R 2 goMu ≃ₗᵢ[R] Lp R 2 goMuI                        -- u |-> u o val
noncomputable def goSemigroupI (t : R>=0) : Lp R 2 goMuI ->L[R] Lp R 2 goMuI        -- goRestr o P_t o goRestr.symm
theorem goSemigroupI_restr (t) (u) : goSemigroupI t (goRestr u) = goRestr (goFullTriple.toDiffusionTriple.semigroup t u)
theorem goSemigroupI_one (t) : goSemigroupI t (1 class) = 1 class                  -- from S11 (conservative_all) for goFullTriple
theorem goI_isFeller : forall t (f : C(GI,R)), exists g : C(GI,R), (goSemigroupI t (clsC goMuI f) : GI -> R) =^m[goMuI] g
```
(`goI_isFeller` from R27 `go_semigroup_poly_cls`, Weierstrass density of polynomials in `C([-1,1])`, `isFeller_of_dense`.)

## M2. Kernels on `GI` and the bridge on `R` (file `R28/GoBridge.lean`)
```
noncomputable def goKernelI : R>=0 -> Kernel GI GI                                 -- Riesz-Markov kernels of `goSemigroupI`
theorem goKernelI_isMarkov (t) (x) : goKernelI t x univ = 1
theorem goKernelI_zero : goKernelI 0 = Kernel.id
theorem goKernelI_add (s t) : goKernelI (s + t) = (goKernelI t).comp (goKernelI s)   -- exact Chapman-Kolmogorov
theorem goKernelI_bind (t) : goMuI.bind (goKernelI t) = goMuI
noncomputable def goRetr : R -> GI                                                  -- clamp to [-1,1]
noncomputable def goMarkovProcessBridge : MarkovProcessBridge goFullTriple.toDiffusionTriple
theorem goMarkovProcessBridge_kernel (t) (x : R) :
    goMarkovProcessBridge.kernel t x = (goKernelI t (goRetr x)).map Subtype.val
theorem goMarkovProcessBridge_isMarkov : forall t x, goMarkovProcessBridge.kernel t x univ = 1
```
So `goMarkovProcessBridge` is a `MarkovProcessBridge` for the ORIGINAL `goFullTriple` on `X = R` (jointly measurable, exact CK, `kappa_0 = id`,
`goMu` invariant, `rep` on bounded measurable `L^2(goMu)` functions), whose kernels from `x` are carried by `[-1,1]`.

## M3. Survey (GAPS table) and cheap closures
The table of every `StandardTriple`/`FullTriple`/`CompactTriple` instance with/without `MarkovProcessBridge` is delivered in `GAPS.md`.
Closures attempted after M1-M2 are frozen below only if cheap (see Status).

## DIFFERENCE FROM BGL
BGL takes Markov kernels as given (Prop. 1.2.3 / Sect. 1.2).  Route here: Feller regularisation (Riesz-Markov + continuity of `x -> P_t f(x)`), as in R16/R24,
carried out on the compact interval because `goMu` has no full support on `R`.  The R16 compact Feller layer is stated for `T : DiffusionTriple X`; it only uses
the semigroup (`nonneg`, sub-Markov, self-adjoint, `P_0 = 1`, `P_{s+t} = P_s P_t`, strong continuity), so it is re-stated for an abstract `SemigroupData`
(`R28/SGData.lean`, `R28/FellerSG.lean`, `R28/FellerSGMeasurable.lean`); no new mathematics.
