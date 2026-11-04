# Round 25, Stream E (stochastic layer): frozen target statements

Written BEFORE any proof (Armstrong method).  Namespace `MarkovTriple.Stochastic.R25`.  No existing file is edited (except
`MarkovTriple.lean`, imports; `GAPS.md`, `ERRATA.md`).
Goal: the first infinite-`mu` instance of the stochastic layer (R24 stream C proved the theory only conditional on `IsFellerC0`):
`(R^d, Lebesgue)`, `lebesgueRdFull d hd` (R24 stream A).  Notation `X = Fin d -> R`, `T = (lebesgueRdFull d hd).toDiffusionTriple`
(`= lebesgueRdDiffusion d hd`, `T.mu = volume`), `gam d = N(0, I_d)`, `a(t) = sqrt(2t)`.

## E1: the explicit heat kernel  (`R25/HeatKernel.lean`)
```
noncomputable def heatKernelRd (d : N) (t : R>=0) : Kernel (Fin d -> R) (Fin d -> R)
  -- heatKernelRd d t x = (gam d).map (fun z => x + sqrt(2t) • z)   (= N(x, 2t I_d))
theorem heatKernelRd_apply_pi (t x) : heatKernelRd d t x = Measure.pi (fun i => gaussianReal (x i) (2 * t))   -- (variance 2t : R>=0)
instance : IsProbabilityMeasure (heatKernelRd d t x)
theorem integral_heatKernelRd (t x) (g : X -> R) (bounded, continuous) : int g d(heatKernelRd d t x) = heatRd (sqrt (2t)) g x
```

## E2: Feller  (`R25/Feller.lean`)
```
theorem lebesgueRd_isFellerC0 (hd : 1 <= d) : IsFellerC0 (lebesgueRdFull d hd).toDiffusionTriple
theorem lebesgueRd_semigroup_cc (hd) (t) (f : C_c(X,R)) (u : Lp R 2 volume) (hu : u =^m f) :
    (T.semigroup t u : X -> R) =^m[volume] heatRd (sqrt (2t)) f        -- extension of semigroup_eq_heatRd from C_c^infty to C_c
```
(the C_0 representative is `heatRd (sqrt (2t)) f`, continuous and vanishing at infinity.)

## E3: identification of the abstract kernels, Markov property, exact CK, invariance, bridge  (`R25/Kernel.lean`)
```
theorem fellerKernelInf_lebesgueRd (hd) (t) (x) : fellerKernelInf (lebesgueRd_isFellerC0 hd) t x = heatKernelRd d t x   -- EVERY x
theorem lebesgueRd_hM (hd) : forall t x, fellerKernelInf (lebesgueRd_isFellerC0 hd) t x univ = 1                        -- discharges `hM`
theorem heatKernelRd_zero : heatKernelRd d 0 = Kernel.id
theorem heatKernelRd_add (s t) : heatKernelRd d (s + t) = heatKernelRd d t o_k heatKernelRd d s        -- exact CK, all x
theorem heatKernelRd_bind (t) : volume.bind (heatKernelRd d t) = volume                                  -- invariance of Lebesgue
noncomputable def brownianBridgeRd (hd) : MarkovProcessBridge (lebesgueRdFull d hd).toDiffusionTriple
  -- := fellerMarkovProcessBridgeInf (lebesgueRd_isFellerC0 hd) (lebesgueRd_hM hd); its kernel is fellerKernelInf = heatKernelRd
theorem brownianBridgeRd_kernel (hd) : (brownianBridgeRd hd).kernel = heatKernelRd d
```
CK is obtained from the abstract `fellerKernelInf_add` through the identification E3; a direct Gaussian-convolution proof is
attempted additionally (the status section says which route was used for which name).

## E4: mass one pointwise for general triples  (`R25/Mass.lean`)
Setting: `X` locally compact, T2, second countable, Borel; `S : StandardTriple X` (field S11 `conservative`),
`[IsFiniteMeasureOnCompacts S.mu] [S.mu.IsOpenPosMeasure]`, `hF : IsFellerC0 S.toDiffusionTriple`, `m_t(x) := (kappa_t(x))(univ) <= 1`
for `kappa = fellerKernelInf hF`.
```
theorem fellerKernelInf_univ_ae (S) (hF) (t) : forall^m x dS.mu, fellerKernelInf hF t x univ = 1          -- S11 + Feller: a.e. only
theorem fellerKernelInf_univ_lsc (hF) (t) : LowerSemicontinuous fun x => fellerKernelInf hF t x univ      -- the direction of semicontinuity
theorem fellerKernelInf_deficit_closed (hF) (t) (c : R) : IsClosed {x | fellerKernelInf hF t x univ <= ENNReal.ofReal c}
theorem fellerKernelInf_deficit_null_Fsigma (S) (hF) (t) :
    exists F : N -> Set X, (forall n, IsClosed (F n)) /\ (forall n, S.mu (F n) = 0) /\
      {x | fellerKernelInf hF t x univ < 1} = Union n, F n      -- the exceptional set is an F_sigma null set (its complement a dense G_delta)
theorem fellerKernelInf_univ_eq_one_of_continuous (S) (hF) (t) (hc : Continuous fun x => (fellerKernelInf hF t x univ).toReal) :
    forall x, fellerKernelInf hF t x univ = 1
noncomputable def fellerMarkovProcessBridgeInf_of_continuous (S) (hF) (hc : forall t, Continuous fun x => (fellerKernelInf hF t x univ).toReal) :
    MarkovProcessBridge S.toDiffusionTriple
```
i.e. S11 + `IsFellerC0` gives mass one a.e. and lower semicontinuity (so mass one on a dense set), NOT everywhere; the additional hypothesis
`hc` (continuity of the total-mass function, "the semigroup maps the constant 1 / `C_b` to continuous functions") is what makes the argument close.
No claim that `hc` follows from S11 + Feller (the lsc direction does not give it; a Feller kernel may lose mass to infinity only at a null closed set --
neither proved nor refuted here).

## E5: finite-`n` converse of Prop. 3.3.17 for `(R^d, Lebesgue)`  (`R25/Converse.lean`)
```
theorem lebesgueRdFull_mem_domain_of_Γ₂_finite (hd : 1 <= d) {n : R>=0inf} (hn : n != top) (hdn : (d : R>=0inf) <= n)
    {f} (hf : f in (lebesgueRdFull d hd).A) (hf2 : MemLp f 2 (lebesgueRdFull d hd).mu)
    (hG : Integrable (FullTriple.G (lebesgueRdFull d hd) f f) (lebesgueRdFull d hd).mu)
    (hG2 : Integrable ((lebesgueRdFull d hd).toDiffusionTriple.Γ₂ f f) (lebesgueRdFull d hd).mu) :
    exists hF : hf2.toLp f in generator.domain, (generator <hf2.toLp f, hF> : X -> R) =^m (lebesgueRdFull d hd).L f
```
an instance of `FullTriple.mem_domain_of_Γ₂_finite` with `rho = 0` and `lebesgueRdFull_CD_iff`.

## DIFFERENCE FROM BGL
BGL treats the heat semigroup on `R^d` through the Gaussian kernel as a known fact; here the route is: Duhamel identification
on `C_c^infty` (R24 A) -> extension to `C_c` by self-adjointness and symmetry of the Gaussian (`<P_t u, g> = <u, P_t g> = <heat u, g>`, density of
`C_c^infty`) -> `C_0` representative `heatRd` -> R24 C Riesz-Markov kernels -> uniqueness (weak continuity) identifies them with `N(x, 2t I)`.
Not a new method.  The general mass statement (E4) has no BGL counterpart (BGL takes Markov kernels as given).

## Status
(appended at the end of the round)
