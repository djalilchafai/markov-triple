# Round 24, Stream C (stochastic layer): frozen target statements

Written BEFORE any proof (Armstrong method).  Namespace `MarkovTriple.Stochastic.R24`.  No existing file is edited.
Goal (GAPS: "Feller extension, Chapman-Kolmogorov and a `MarkovProcessBridge` for infinite `mu`; exact all-time semigroup for
abstract compact triples").  Source: BGL Sect. 1.2-1.4 and the standard Feller route (Riesz-Markov-Kakutani on `C_c`, uniqueness of
continuous representatives for full-support `mu`).

## Setting
`X` locally compact, `T2`, second countable, Borel.  `T : DiffusionTriple X` with `[IsFiniteMeasureOnCompacts T.mu]`
(`T.mu` may be infinite) and `[T.mu.IsOpenPosMeasure]` (full support: a.e.-equal continuous functions are equal).

## Hypothesis: C_0-Feller
```
def IsFellerC0 (T : DiffusionTriple X) : Prop :=
  forall (t : R>=0) (f : C_c(X,R)) (u : Lp R 2 T.mu), (u : X -> R) =^m[T.mu] f ->
    exists g : C_0(X,R), (T.semigroup t u : X -> R) =^m[T.mu] g
```
(the semigroup maps `C_c` into classes of `C_0`: the classical Feller property; for compact `X` it is `IsFeller`, R16.)

## C1: exact kernel semigroup for infinite `mu`  (`R24/Feller.lean`)
For `hF : IsFellerC0 T` there is `fellerKernelInf hF : R>=0 -> Kernel X X` (defined at EVERY point) with
```
theorem fellerKernelInf_subMarkov : forall t x, fellerKernelInf hF t x univ <= 1
theorem fellerKernelInf_integral_cc (t) (f : C_c(X,R)) (u : Lp R 2 T.mu) (hu : u =^m f) :
    exists g : C_0(X,R), (forall x, g x = int y, f y d(fellerKernelInf hF t x)) /\ (T.semigroup t u : X -> R) =^m g
theorem fellerKernelInf_zero : fellerKernelInf hF 0 = Kernel.id
theorem fellerKernelInf_add (s t) : fellerKernelInf hF (s + t) = fellerKernelInf hF t o_k fellerKernelInf hF s   -- EXACT, all x, all s t
theorem fellerKernelInf_bind_le (t) : T.mu.bind (fellerKernelInf hF t) <= T.mu
theorem fellerKernelInf_rep (t) (g : X -> R) (hg : Measurable g) (hb : exists C, forall x, |g x| <= C) (hL : MemLp g 2 T.mu) :
    (T.semigroup t (hL.toLp g) : X -> R) =^m[T.mu] fun x => int y, g y d(fellerKernelInf hF t x)
noncomputable def fellerKernelRepInf : KernelRepresentation T      -- with the exact CK above
noncomputable def fellerSemigroupInf : SubMarkovKernelSemigroup X
```
Uniqueness (everywhere): `fellerKernelInf_unique`: any finite-measure kernel `kappa'` with `x |-> int f d(kappa' x)` continuous for
`f in C_c` and representing `P_t` on `C_c` a.e. equals `fellerKernelInf hF t` at every point.

## C2: joint measurability and `MarkovProcessBridge`  (`R24/Bridge.lean`)
```
theorem fellerKernelInf_measurable_joint : Measurable fun p : R>=0 x X => fellerKernelInf hF p.1 p.2
noncomputable def fellerMarkovProcessDataInf : MarkovProcessSemigroupData X
noncomputable def fellerMarkovProcessBridgeInf (hM : forall t x, fellerKernelInf hF t x univ = 1) : MarkovProcessBridge T
theorem fellerKernelInf_bind (hM) (t) : T.mu.bind (fellerKernelInf hF t) = T.mu
```
`MarkovProcessBridge` requires equality invariance, which forces Markov kernels; `hM` (pointwise mass 1 for every `t`, `x`) is an
explicit hypothesis (an a.e. statement is what conservativity of the semigroup gives; no claim is made that it follows).

## C3: abstract compact triples: Feller is exactly what an exact all-time semigroup needs  (`R24/Compact.lean`)
`X` compact (so the above specialises), `T` with finite full-support `mu`:
```
theorem isFeller_iff_exists_continuous_kernel :
    IsFeller T <-> exists kappa : R>=0 -> Kernel X X, (forall t x, kappa t x univ <= 1) /\
      (forall t (f : C(X,R)), Continuous fun x => int y, f y d(kappa t x)) /\
      (forall t (f : C(X,R)), (T.semigroup t (clsC T.mu f) : X -> R) =^m[T.mu] fun x => int y, f y d(kappa t x))
theorem feller_exact_ck_unique : -- two such (weakly continuous) kernel families coincide at every point, hence the one with
                                -- exact CK is unique
```
i.e. the additional hypothesis that makes exact all-time Chapman-Kolmogorov provable for kernels is weak-Feller continuity of the
kernels (equivalently the Feller property of `P_t` on `C(X)` for full-support `mu`); without it R22-E3-2 shows exact CK can fail.
No claim is made that a non-Feller `P_t` has no exact all-time semigroup (not proved, not refuted).

## C4: non-vacuity (`R24/OU.lean`, optional)
`R24.ou_isFellerC0 : IsFellerC0 ouDiff` (OU on `R`: finite `gamma`, full support, non-compact).  Lebesgue/Gibbs infinite instances:
NOT claimed.

## DIFFERENCE FROM BGL
BGL (Sect. 1.2, Remark after Def. 1.2.1) assumes a kernel/Feller regularity and does not spell out the regularisation; here it is
the Riesz-Markov-Kakutani route on `C_c(X)` with `C_0`-Feller input and uniqueness of continuous representatives.  Not a new method.

## Status (end of round; statements above NOT weakened)
Files: `Operator, Cutoff, Feller, Extend, Exact, Measurable, Bridge, Compact, Instances, OU, AxiomCheckR24C` (`Stochastic/R24/`).  No `sorry`,
no `set_option`, 0 warnings, axioms only `propext, Classical.choice, Quot.sound`.  Full `lake build` green; `check_frozen.py` OK.

PROVED, with the exact statements above (names as listed, in `MarkovTriple.Stochastic.R24`): `IsFellerC0`, `fellerKernelInf`,
`fellerKernelInf_subMarkov`, `_integral_cc`, `_zero`, `_add` (EXACT CK, all `s,t,x`), `_bind_le`, `_rep`, `fellerKernelRepInf`,
`fellerSemigroupInf`, `fellerKernelInf_unique`, `fellerKernelInf_measurable_joint`, `fellerMarkovProcessDataInf`,
`fellerKernelInf_bind`, `fellerMarkovProcessBridgeInf`, `isFeller_iff_exists_continuous_kernel`, `ou_isFellerC0`.
Route: `Qop` (continuous `C_0` representative, unique by full support) -> `RealRMK.rieszMeasure` on `C_c` (Mathlib) ->
extension of the representation to `C_0 cap L^2` by cut-offs `chi_n h -> h` in `L^2` (`fellerKernelInf_rep_C0`) -> continuity of
`x |-> int h dkappa_s(x)` for `h in C_0` (uniform limit) -> exact CK by comparing two continuous functions equal a.e.
(`Qop_add_time`) -> sub-invariance by R23 `bind_le_of_rep` -> joint measurability: for fixed `x`, `t |-> Q_t f (x)` is a pointwise limit
of the `L^2`-continuous `t |-> <P_t f, psi_k>` (bumps `psi_k` at `x`), then Caratheodory (`measurable_uncurry_of_continuous_of_measurable`)
-> bridge: reversibility on compact sets + `B = K_n up X` gives `mu.bind kappa_t = mu` when every `kappa_t(x,X) = 1`.

Deviations / additions (log, no weakening):
(a) C3 `feller_exact_ck_unique` is realised as `weakFeller_kernel_unique`, `weakFeller_zero`, `weakFeller_add` (for the predicate
    `IsWeakFellerRep`): every weakly continuous representing family has exact CK and `kappa_0 = id` and is unique pointwise.
(b) extra, not in the frozen list: `isFellerC0_iff_exists_C0_kernel` (C_0 analogue of the iff), `isFellerC0_of_isFeller` (compact `IsFeller` =>
    `IsFellerC0`), `fellerKernelInf_eq_fellerKernel` (agrees with R16 kernels), `circle_isFellerC0`, `sphere_isFellerC0`,
    `circle_fellerKernelInf_eq`, `ou_fellerKernelInf_eq`, `ouMarkovProcessBridgeInf`, `fellerKernelInf_reversible`.
(c) the hypotheses `[IsFiniteMeasureOnCompacts T.mu]`, `[T.mu.IsOpenPosMeasure]`, `IsFellerC0 T` are all genuinely used; `hM` only for the bridge.

NOT done / honest limits:
* **No infinite-`mu` instance of `IsFellerC0`.**  The theory of C1-C2 is only proved conditional on `IsFellerC0 T`; the only non-compact
  instance is OU (finite `gamma`).  `IsFellerC0 lebesgueFull.toDiffusionTriple` (heat semigroup on `R` with infinite `volume`) is OPEN:
  it needs the identification of the abstract semigroup with Gaussian convolution (F8 / heat-kernel identification, R23-R).  So "Feller
  extension for infinite `mu`" is closed as a CONDITIONAL theorem, not for a named infinite example.
* `MarkovProcessBridge` for infinite `mu` needs pointwise `kappa_t(x,X) = 1` (`hM`) because the structure demands `mu.bind kappa_t = mu`.
  Conservativity of the semigroup gives it only a.e. (R23 S4); passage a.e. -> every `x` is NOT proved (lower semicontinuity of
  `x |-> kappa_t(x,X)` goes the wrong way).  Without `hM` one has `fellerMarkovProcessDataInf` (sub-Markov, sub-invariant).
* Full support `mu` is assumed (continuous representatives unique); the general case (restriction to `supp mu`) is not done.
* Exact all-time semigroup for abstract compact triples: the answer proved is "exactly under Feller" (C3).  NOT proved, NOT refuted: that
  a non-Feller `P_t` has no exact all-time kernel semigroup (Kuznetsov/right-process type question).  Feller itself is a hypothesis, not
  derived from the triple axioms (open since R17).

Proposed ERRATA rows (do not edit `ERRATA.md`):
| R24-C-1 | INFO (scope) | Exact Feller kernels, exact CK, sub-invariance, `KernelRepresentation`, joint measurability and `MarkovProcessSemigroupData` for `T` with `mu` finite on compacts (infinite allowed), full support, `IsFellerC0 T`: `R24.fellerKernelInf`, `fellerKernelInf_add`, `fellerKernelInf_measurable_joint`. CONDITIONAL on `IsFellerC0`; only non-compact instance OU (finite `gamma`); no infinite-`mu` instance (Lebesgue open). | `Stochastic/R24/*` |
| R24-C-2 | INFO (scope) | `fellerMarkovProcessBridgeInf` needs the explicit pointwise hypothesis `hM : kappa_t(x,X)=1`; a.e. mass one is not enough for equality invariance in this construction. | `R24/Bridge.lean` |
| R24-C-3 | INFO (characterisation) | `isFeller_iff_exists_continuous_kernel`, `weakFeller_add`, `weakFeller_zero`: for compact full-support triples, a kernel representation is weak-Feller iff `P_t` is Feller, and then exact CK holds and the kernels are unique at every point; complements the R22-E3-2 obstruction (without continuity exact CK can fail). Existence of an exact semigroup for a non-Feller `P_t` remains open. | `R24/Compact.lean` |
Proposed `MarkovTriple.lean` imports: already added (`Stochastic.R24.Operator ... AxiomCheckR24C`).
Proposed GAPS update: see the "Round 24 stream C" paragraph appended to `BGL/Theory/GAPS.md`.
