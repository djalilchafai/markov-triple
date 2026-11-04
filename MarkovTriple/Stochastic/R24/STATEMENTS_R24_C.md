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
