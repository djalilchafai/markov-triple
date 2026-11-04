# Round 27, Stream K (stochastic layer): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R27`.  Two questions left open by R25-E and R23/R24.

## K1: pointwise mass one for Feller + S11  (`R27/Mass.lean`)
Setting as in R25-E4: `X` locally compact T2 second countable Borel, `S : StandardTriple X`, `[IsFiniteMeasureOnCompacts S.mu]`,
`[S.mu.IsOpenPosMeasure]`, `hF : IsFellerC0 S.toDiffusionTriple`, `kappa = fellerKernelInf hF`.  Write `m_t(x) = kappa_t(x) univ`.
Decision made BEFORE proving (mathematical analysis, see Status for the outcome): S11 + Feller alone is NOT shown to give `m_t(x) = 1`
at every `x`; no formal proof and no formal counterexample is claimed.  What is frozen is the conditional theory:
```
theorem fellerKernelInf_univ_antitone (hF) (s t) (x) : kappa_(s+t) x univ <= kappa_s x univ                       -- no S11 needed
theorem fellerKernelInf_univ_add_of_ac (S) (hF) (s t) (x) (hac : kappa_s x << S.mu) :
    kappa_(s+t) x univ = kappa_s x univ                                                                       -- S11 (a.e. mass one) + CK
theorem fellerKernelInf_univ_const_of_ac (S) (hF) (hac : forall s, 0 < s -> forall x, kappa_s x << S.mu)
    (s t : R>=0) (hs : 0 < s) (ht : 0 < t) (x) : kappa_s x univ = kappa_t x univ                              -- mass is time-independent on t > 0
theorem fellerKernelInf_univ_eq_one_of_ac_init (S) (hF) (hac : forall s, 0 < s -> forall x, kappa_s x << S.mu)
    (hinit : forall x (f : C_c(X,R)), Tendsto (fun t => Qop hF t f x) (nhdsWithin 0 (Ioi 0)) (nhds (f x)))
    (t) (x) : kappa_t x univ = 1
noncomputable def fellerMarkovProcessBridgeInf_of_ac_init (S) (hF) (hac) (hinit) : MarkovProcessBridge S.toDiffusionTriple
```
i.e. absolute continuity of the kernels (`kappa_s(x,.) << mu`, `s > 0`, every `x`) + pointwise initial condition (`Q_t f(x) -> f(x)`)
close the gap.  Neither hypothesis follows from S11 + Feller by anything proved here.

## K2: Feller property of `goFullTriple`  (`R27/Gegenbauer.lean`)
`goFullTriple : FullTriple R` lives on the space `X = R` (not on `[-1,1]`), `mu = (3/4)(1-x^2)dx` on `(-1,1)`, zero outside.
```
theorem goMu_not_isOpenPos : not (goFullTriple.mu.IsOpenPosMeasure)                      -- every R24 `fellerKernelInf` needs this instance
theorem go_semigroup_poly (t) (p : Polynomial R) (hp : MemLp (fun x => p.eval x) 2 goFullTriple.mu) :
    exists q : Polynomial R, (goFullTriple.toDiffusionTriple.semigroup t (hp.toLp _) : R -> R) =^m[goFullTriple.mu] fun x => q.eval x
theorem goFull_isFellerC0 : IsFellerC0 goFullTriple.toDiffusionTriple
```
(`IsFellerC0` is a well-formed `Prop` on `X = R` without `IsOpenPosMeasure`; with `mu` supported on `[-1,1]` it says exactly that `P_t[f]`
has a continuous version on `[-1,1]` for `f` continuous; it does not give kernels/bridge on `R` since `IsOpenPosMeasure` fails.)

## DIFFERENCE FROM BGL
BGL takes Markov kernels as given.  K2 route: polynomials are in the generator domain (R24-B converse, no completeness) and form finite-dimensional
`L`-invariant subspaces, on which `P_t` is explicit; density (Weierstrass) + sup-norm contraction.  Not a new method.

## Status
(to be appended at the end of the round)
