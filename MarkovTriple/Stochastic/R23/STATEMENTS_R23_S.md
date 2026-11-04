# Round 23, Stream S (stochastic layer): frozen target statements

Written BEFORE any proof (Armstrong method).  Namespace `MarkovTriple.Stochastic.R23`.  No existing file is edited.
Goal: the Round 22 non-compact Riesz-Markov kernel representation (`R22.exists_kernel_of_posContraction_noncompact`,
FINITE `mu`) for INFINITE sigma-finite `mu` (Lebesgue on `R`, Gibbs-type infinite measures).

## Hypotheses (the "correct" ones for infinite `mu`)
`X` locally compact, `T2`, second countable, Borel; `mu` locally finite (`IsFiniteMeasureOnCompacts mu`; then `mu` is sigma-finite;
without it `C_c not-subset L^2(mu)`).  `P : L^2(mu) ->L[R] L^2(mu)` with
* `hpos`: `0 <= u` a.e. `=> 0 <= P u` a.e.   (positivity preserving),
* `hle`: `u <= 1` a.e. `=> P u <= 1` a.e.     (`L^infty`-contractive / sub-Markov; `u in L^2`, `1 notin L^2` is irrelevant),
* for sub-invariance only: `hsa : IsSelfAdjoint P` (symmetric: BGL's semigroups are `mu`-symmetric).
The finite-`mu` hypothesis `hmass : int P u <= int u` is NOT used (it is not meaningful for `u notin L^1`); on a finite measure
it follows from `hsa` and `hle` (`<P u,1> = <u,P 1> <= <u,1>`), and for infinite `mu` the analogue is proved here for the
`lintegral` (`int^- P f <= int f` for `f in C_c`, `f >= 0`) and gives `mu.bind kappa <= mu`.
For a `DiffusionTriple` all three hold (`semigroup_nonneg`, `semigroup_le_one`, `semigroup_isSelfAdjoint`: all stated
with NO finiteness assumption on `T.mu`), so `lebesgueFull`'s semigroup satisfies them.

## S1: abstract kernel representation for infinite `mu`  (`R23/Exhaustion.lean`, `R23/AEKernel.lean`)
`C_0(X,R)` = `ZeroAtInftyContinuousMap`.
```
theorem exists_kernel_of_posContraction_locFinite {mu : Measure X} [IsFiniteMeasureOnCompacts mu]
    (P : Lp R 2 mu ->L[R] Lp R 2 mu)
    (hpos : forall u, 0 <=^m u -> 0 <=^m P u) (hle : forall u, u <=^m 1 -> P u <=^m 1) :
    exists kappa : Kernel X X, (forall x, kappa x univ <= 1) /\
      forall (f : C_0(X,R)) (u : Lp R 2 mu), u =^m f -> P u =^m (fun x => int y, f y d(kappa x))
theorem exists_kernel_of_posContraction_locFinite_subInv  -- same hypotheses plus (hsa : IsSelfAdjoint P)
    : exists kappa : Kernel X X, (forall x, kappa x univ <= 1) /\ mu.bind kappa <= mu /\
      forall (f : C_0(X,R)) (u : Lp R 2 mu), u =^m f -> P u =^m (fun x => int y, f y d(kappa x))
```
(Note: `u =^m f` with `u in L^2(mu)` forces `f in L^2(mu)`: the representation is on `C_0 cap L^2`, in particular on `C_c`.)
Supporting statement (abstract compact lemma, `R23/AEKernel.lean`): for `Y` compact `T2` second countable Borel, any measure `m`, and a
family `F : C(Y,R) -> Y -> R` of measurable functions that is a.e.-additive, a.e.-homogeneous, a.e.-positive with `F 1 <= 1` a.e.,
there is a sub-Markov kernel `kappa` with `F f =^m  y |-> int f d(kappa y)` for every `f`
(`exists_kernel_of_aeLinear`; the R15 proof, with `L^2`-continuity replaced by the sup-norm bound `|F f| <= ||f||`).

## S2: `KernelRepresentation` for a `DiffusionTriple` with infinite `mu`  (`R23/Triple.lean`)
```
variable (T : DiffusionTriple X) [IsFiniteMeasureOnCompacts T.mu]    -- T.mu may be infinite
noncomputable def ncKernelRepInf : KernelRepresentation T
theorem ncKernelRepInf_subInvariant (t) : T.mu.bind ((ncKernelRepInf T).kappa t) <= T.mu
theorem ncKernelRepInf_C0 (t) (f : C_0(X,R)) (u : Lp R 2 T.mu) (hu : u =^m f) :
    T.semigroup t u =^m fun x => int y, f y d((ncKernelRepInf T).kappa t x)
```
`KernelRepresentation` itself needs NO generalisation: its fields (`kappa`, `subMarkov`, `rep` for bounded measurable `g` with
`MemLp g 2 T.mu`) make sense for infinite `mu`; `kernelRep_of_dense` (R15, `RepExtend.lean`) is already stated with no finiteness
assumption.  What needs generalising and is NOT done here: `ck_integral`/`ck_ae`/`exists_exact_ck` (they assume `[IsFiniteMeasure T.mu]` to
get `MemLp` of bounded `g`; for infinite `mu` they need `g in L^2 cap L^inf`).  Reported, not proved (unless stated below).

## S3: non-vacuity for `lebesgueFull`  (`R23/Lebesgue.lean`)
```
noncomputable example : KernelRepresentation lebesgueFull.toDiffusionTriple := ncKernelRepInf _
theorem lebesgue_kernelRep_subInvariant (t) : volume.bind ((ncKernelRepInf lebesgueDiffusion).kappa t) <= volume
```
(`lebesgueDiffusion.mu = volume` is infinite, `IsFiniteMeasureOnCompacts volume` holds.)

## S4: conservativity => Markov kernels  (`R23/Markov.lean`, attempted only if cheap)
Precise statement.  For a `StandardTriple S` on `X` (so `S.conservative`: `P_t u_n -> 1` a.e. along exhaustion sequences):
```
theorem ncKernelRepInf_univ_ae (S : StandardTriple X) [IsFiniteMeasureOnCompacts S.mu] (t) :
    forall^m x dS.mu, (ncKernelRepInf S.toDiffusionTriple).kappa t x univ = 1
theorem exists_markovRep (S : StandardTriple X) [IsFiniteMeasureOnCompacts S.mu] :
    exists K : KernelRepresentation S.toDiffusionTriple, K.IsMarkovRep
```
Route: rep on bounded measurable `u_n in A_0 subset L^2` (S2) and `0 <= u_n <= 1`, `P_t u_n -> 1`, so `kappa_t(x,X) >= int u_n dkappa_t = P_t u_n(x) -> 1`;
then Dirac-redefinition on the null measurable set `{kappa(x,X) != 1}` (as `rieszKernelRep_markov`).  NOT claimed: sub-invariance of the
modified kernel is not part of the statement (it holds, Dirac modification on a null set, but is not claimed), exact CK for all
times, Feller property.

## DIFFERENCE FROM BGL
BGL (Sect. 1.2, kernel/density representation) assumes the representation or gets it from Feller/Hunt regularity; here it is
constructed per fixed `t` by Riesz-Markov through the one-point compactification, a.e. identification only.  New in this
round: infinite `mu`.  The route is NOT the weighted `L^2(h^2 mu)` reduction nor a diagonal argument of finite kernels:
it is a direct monotone-exhaustion construction (see Plan).  Kernels are sub-Markov only on non-compact `X` (mass lost at
infinity), except under S4.  The representation is for `C_0 cap L^2` (not all of `C_0`: `C_0 notin L^2(mu)` in general), and
then on all bounded `L^2` measurable functions for triples.

## Plan (choice with justification; BEFORE coding)
Plans (1) weight `h = R_1 g` and (3) diagonal argument were rejected: (1) needs `P_t h <= e^t h` for the semigroup and an
isometry `L^2(h^2 mu) = L^2(mu)` plus re-extension from continuous to measurable test functions (and works only for semigroups,
or after a Neumann-series excessive weight); (3) needs a.e.-monotonicity of the `kappa_n` as MEASURES (countable dense family
of test functions) and a monotone limit of measures.  Chosen: variant of (2) that never builds measures at finite stages:
for `f in C(X^+)` (`X^+` the one-point compactification), `F f := lim_n P(1_{K_n} f|_X)` (a.e. limit; `K_n` compact exhaustion with
`K_n subset int K_{n+1}`, monotone and bounded by `||f||` for `f >= 0`, by `hpos`, `hle`), a.e.-linear, positive, `F 1 <= 1`;
Riesz-Markov on the compact `X^+` (the R15 argument, `exists_kernel_of_aeLinear`) gives `kappa^+`; `kappa = comap (coe) kappa^+`.
Representation on `C_0 cap L^2`: `1_{K_n} f -> f` in `L^2` so `P(1_{K_n} f) -> P u` in `L^2` and a.e. along a subsequence.
Sub-invariance from `hsa`: `int_{K_n} P f = <f, P 1_{K_n}> <= int f`, then compact sets (Urysohn + outer regularity) and inner regularity.

## Status
(to be filled after the proofs)
