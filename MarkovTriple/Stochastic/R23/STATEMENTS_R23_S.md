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
Files (all in `MarkovTriple/Stochastic/R23/`): `AEKernel.lean`, `Exhaustion.lean`, `SubInv.lean`, `Triple.lean`, `Markov.lean`,
`Lebesgue.lean`, `AxiomCheck.lean`.  Build: 0 warnings, no `sorry`, no `set_option`, no new axiom; `#print axioms` of every theorem
below = only propext, Classical.choice, Quot.sound.  No existing file edited (R22 files are imported, not modified).

PROVED (all statements above, none weakened):
* S1: `R23.exists_kernel_of_aeLinear` (compact lemma), `R23.exists_kernel_of_posContraction_locFinite` (`Exhaustion.lean`),
  `R23.exists_kernel_of_posContraction_locFinite_subInv` (`SubInv.lean`; the sub-invariance part is `R23.bind_le_of_rep`,
  with `R23.lintegral_P_le`: `int^- P u <= int u` for `0 <= u in L^2 cap L^1`, `P` symmetric).  Auxiliary: `abs_le_norm_of_aeLinear`
  (stated for `F : C(Y,R) -> Z -> R`, slightly more general than needed), `tendsto_tr` (`1_{K_n} f -> u` in `L^2`), `rr_tendsto_ae`.
* S2: `R23.ncKernelRepInf : KernelRepresentation T`, `ncKernelRepInf_subInvariant`, `ncKernelRepInf_C0`, `cc_dense`
  (`C_c` dense in `L^2` for `mu` finite on compacts).  `KernelRepresentation` is NOT modified and needs no generalisation:
  `kernelRep_of_dense` was already finiteness-free.  NOT generalised (reported): `KernelRepresentation.ck_integral`, `ck_ae`
  (assume `[IsFiniteMeasure T.mu]` to make bounded `g` an `L^2` function; for infinite `mu` they need `g in L^2 cap L^inf`) and
  `exists_exact_ck`/`nc_exists_exact_ck` (the whole `ExactCK.lean` variable block carries `[IsFiniteMeasure T.mu]`).  So: NO
  Chapman-Kolmogorov (a.e. or exact) is claimed for the infinite-`mu` kernels.
* S3: `R23.lebesgueKernelRep : KernelRepresentation lebesgueFull.toDiffusionTriple`, `lebesgueKernelRep_subInvariant`
  (`volume.bind kappa_t <= volume`), `lebesgue_locFin` (instance), and `example : lebesgueFull.mu univ = infty` (genuinely infinite).
  Also `example : KernelRepresentation ouDiff := ncKernelRepInf ouDiff` in `AxiomCheck.lean` (the infinite construction contains the
  finite case; unlike R22 it needs no `hmass`).
* S4 (cheap, done): `R23.ncKernelRepInf_univ_ae` (`kappa_t(x,X)=1` a.e. for a `StandardTriple`), `R23.exists_markovRep`
  (`IsMarkovRep` everywhere after Dirac modification on a null set), `R23.lebesgue_exists_markovRep`.

Deviations from the statement text (log, no weakening): (a) names in S3: `lebesgueKernelRep(_subInvariant)` and
`lebesgueFull.toDiffusionTriple` instead of `ncKernelRepInf lebesgueDiffusion` (same triple: defeq, checked by the type checker);
(b) `exists_kernel_of_posContraction_locFinite_subInv` is in `SubInv.lean`, not `Exhaustion.lean`; (c) the S4 Markov kernels
`K` of `exists_markovRep` come with `IsMarkovRep` and the representation, but their sub-invariance is not stated (it holds, null-set
modification; not formalised); (d) hypotheses used: `IsFiniteMeasureOnCompacts mu`, `hpos`, `hle`, and `hsa` only for sub-invariance,
exactly as announced; `u <= 1 => P u <= 1` is the correct `L^infty` hypothesis (the finite-`mu` `hmass` is dropped).
Hypotheses are satisfied by the semigroup of any `DiffusionTriple` (`semigroup_nonneg/le_one/isSelfAdjoint`, proved with no finiteness).

Limits of the result (honest scope):
* Representation holds a.e. and for each fixed `t` (Riesz-Markov per `t`), as in R22; no exact all-times CK, no Feller property,
  no `MarkovProcessBridge` (R22-E3-2 obstruction still applies).
* On `C_0 cap L^2(mu)` (resp. bounded measurable `L^2` functions for triples), not on all of `C_0` (`C_0 notin L^2(mu)` for infinite `mu`).
* Kernels are only sub-Markov in S1/S2 (mass lost at infinity); conservativity of the semigroup in the sense of `StandardTriple.conservative`
  (monotone limits along exhaustion sequences; the only meaning of `P_t 1 = 1` for infinite `mu`) gives Markov kernels (S4).
  A stand-alone `DiffusionTriple` with conservative semigroup but no `StandardTriple` structure (ergodicity field) is not treated
  (the proof only uses `conservative`; one could factor it out).
* No Gibbs-type infinite-measure instance was built (only `lebesgueFull`); any `DiffusionTriple` on a locally compact second countable
  Borel space with `mu` finite on compacts now has `ncKernelRepInf`.
* Mathlib input used: `CompactExhaustion.choice`, `measurable_limit_of_tendsto_metrizable_ae`, Urysohn (`exists_continuous_one_zero_of_isCompact`),
  regularity of Radon measures on second countable locally compact T2 spaces, plus R15 `exists_posFunctional`/`exists_measure_of_pos`
  (Hahn-Banach/RMK) and R22 `OnePoint` second countability.  The one-point compactification is used only for the compact RMK step.

Proposed ERRATA rows (do not edit `ERRATA.md`):
| R23-S-1 | INFO (scope; supersedes R22-E3-1 "finite `mu` only") | Non-compact Riesz-Markov kernel representation now for `mu` finite on compacts (infinite allowed): `R23.exists_kernel_of_posContraction_locFinite(_subInv)`, hypotheses positivity + `L^infty`-contractivity (+ symmetry for sub-invariance); on `C_0 cap L^2`. The R22 finite theorem is unchanged and still valid. | `Stochastic/R23/Exhaustion.lean`, `SubInv.lean` |
| R23-S-2 | INFO (route, DIFFERS FROM BGL and from R22) | No weight `h = R_1 g`, no diagonal argument: `F f = lim_n P(1_{K_n} f)` on `C(X^+)` plus the R15 RMK argument with sup-norm bound (`exists_kernel_of_aeLinear`). | `Stochastic/R23/AEKernel.lean` |
| R23-S-3 | INFO | `KernelRepresentation` for `DiffusionTriple` with infinite `mu`: `ncKernelRepInf`; `lebesgueKernelRep` for `lebesgueFull` (`volume`); structure unchanged. | `R23/Triple.lean`, `R23/Lebesgue.lean` |
| R23-S-4 | INFO (scope, limit) | `ck_integral`, `ck_ae`, `exists_exact_ck` still assume finite `T.mu`; no CK is claimed for the infinite-`mu` kernels. | `KernelRep.lean`, `ExactCK.lean` (unchanged) |
| R23-S-5 | INFO | Conservative `StandardTriple` on infinite `mu` => a.e. mass-one kernels and `IsMarkovRep` representation (`exists_markovRep`, `lebesgue_exists_markovRep`). | `R23/Markov.lean` |
Proposed `MarkovTriple.lean` imports: `MarkovTriple.Stochastic.R23.Lebesgue`, `MarkovTriple.Stochastic.R23.AxiomCheck`
(the others are imported transitively).  Proposed GAPS update: Round 17 item (2) Riesz-Markov kernel representation: closed for `mu` finite
on compacts (infinite included); Feller extension, CK/Markov-process bridge for non-compact (infinite) case still OPEN.
