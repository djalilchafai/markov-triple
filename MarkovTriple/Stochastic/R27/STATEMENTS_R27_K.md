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
End of round.  Files: `Mass, GoAlg, GoPoly, GoSem, GoFeller, AxiomCheckR27K` (`Stochastic/R27/`).  No `sorry`, no `set_option`, 0 warnings,
axioms only `propext, Classical.choice, Quot.sound`; full `lake build` green.  Statements above NOT weakened.

PROVED (namespace `MarkovTriple.Stochastic.R27`), K1: `fellerKernelInf_univ_antitone`, `fellerKernelInf_univ_add_of_ac`,
`fellerKernelInf_univ_const_of_ac`, `fellerKernelInf_univ_eq_one_of_ac_init`, `fellerMarkovProcessBridgeInf_of_ac_init` (plus `fellerKernelInf_univ_add`,
`kappa_(s+t)(x,X) = int kappa_t(y,X) d kappa_s(x,y)`).  K2: `goMu_not_isOpenPos` (also `goμ_not_isOpenPos`), `go_semigroup_poly` (also the class form
`go_semigroup_poly_cls`), `goFull_isFellerC0`; supporting: `go_smooth_mem_domain` (every smooth `f : R -> R` is in the generator domain of `goFullTriple`
with `G f = L f`, from the R24-B converse), `go_semigroup_eigen`, `exists_eigen_decomp` (finite spectral decomposition via `aeval`/Lagrange-free induction),
`aeval_chi_goM` (`prod_{j<n}(M + j(j+3))` kills `degreeLT n`), `abs_semigroup_le`, `go_approx`, `go_limit`.

DECISION on K1 (honest): the question "does S11 + `IsFellerC0` (+ full support, locally compact) force `kappa_t(x,X) = 1` at EVERY `x`?" is NOT settled.
No proof and no formal counterexample.  What was found:
* by CK, `x |-> m_t(x)` is non-increasing in `t`, and `m_(s+t)(x) = int m_t d kappa_s(x,.)`; a.e. mass one transfers to a pointwise identity exactly when
  `kappa_s(x,.) << mu`, but it gives only `m_(s+t)(x) = m_s(x)`: the pointwise deficit is TIME-INDEPENDENT for `t > 0`, i.e. a bad point is a point killed
  instantaneously ("dead point").  Absolute continuity alone does not exclude it.
* a pointwise initial condition `Q_t f(x) -> f(x)` excludes it (`m_t(x) >= Q_t f(x) -> 1` for a bump `f`); both hypotheses hold for the heat kernel.
* a counterexample would need `kappa_t(x_n,.)` to lose mass to infinity as `x_n -> p` with `kappa_t(x,X) = 1` for a.e. `x`.  A jump-process heuristic
  (`L f = lambda(x)(f(1/x) - f(x))`, `lambda(x) = 1/|x|` near `0`; not verified in detail) would do this, but is not a diffusion (the Leibniz/chain-rule axioms of a `DiffusionTriple` fail),
  so it is not a `StandardTriple`.  For rotationally symmetric/one-dimensional diffusions the radial process is monotone (stopping time from `x` to a fixed
  radius is stochastically decreasing in the starting radius), which heuristically excludes escape; this is not formalised and is not claimed as a theorem.
  Nothing was built for a diffusion counterexample; no claim that one exists or not.

K2 outcome: `IsFellerC0 goFullTriple.toDiffusionTriple` HOLDS, on the space `X = R` (the space of `goFullTriple : FullTriple R`).  Since `goFullTriple.mu` is supported on
`[-1,1]`, informally it says that `P_t[f]` has a continuous version on `[-1,1]` for continuous `f` (the equivalence is not formalised; proved through Weierstrass density of polynomials,
invariance of polynomials under `P_t`, and the sup-norm contraction of `P_t`).  NOT done: kernels and a `MarkovProcessBridge` for `goFullTriple`.  Reason (formalised):
`goMu_not_isOpenPos` shows `IsOpenPosMeasure` fails on `X = R`, which every R24 construction (`Qop`, `fellerKernelInf`, bridge) needs; building the bridge needs a
transport of the triple to `[-1,1]` (compact, `IsFeller`) or `(-1,1)` (locally compact, `IsFellerC0`) -- a re-presentation of `goFullTriple` on a subtype -- not attempted.
No claim on boundary behaviour beyond continuity of `P_t f` up to `+-1`.

Log of small deviations (no weakening): (a) K2 also provides the non-frozen alias `goμ_not_isOpenPos` and `go_semigroup_poly_cls`; (b) K1 frozen names/hypotheses are
as written (the hypothesis `hac` is only for `s > 0`, every `x`).
