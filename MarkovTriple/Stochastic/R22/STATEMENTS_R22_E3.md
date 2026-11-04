# Round 22, Stream E3 (stochastic layer): frozen target statements

Written BEFORE any proof (Armstrong method).  Namespace `MarkovTriple.Stochastic.R22`.  No existing file is edited.
Source: BGL Sect. 1.2-1.4 (kernel/density representation, Chapman-Kolmogorov, `mu`-invariance) and the
Riesz-Markov-Kakutani representation; Mathlib's `RealRMK` is used only through the library's compact-case
`exists_kernel_of_posContraction` (R15).

## Part (i): exact CK / `MarkovProcessBridge` for ALL times
Status BEFORE this stream (re-verified, nothing new to prove): OU (`ouMarkovProcessBridge`), circle
(`circleMarkovProcessBridge`), every conservative Feller triple (`fellerMarkovProcessBridge`) and the zonal `S^3`
(`sphereMarkovProcessBridge`) already have exact CK for every `t : R>=0` (not countable times).  No further statement is
claimed in (i).

## Part (ii): plain Riesz kernels (no Feller): exact obstruction, NOT a bridge  (`R22/Obstruction.lean`)
The Riesz kernels `rieszKernel T t` are only characterised (by `Classical.choose`) by: sub-Markov, `P_t [f] = kappa_t f` a.e. for
`f in C(X)`.  Claim (obstruction): these (and the full `KernelRepresentation` axioms) do not imply exact CK, so no proof of a
`MarkovProcessBridge` can start from them.
```
theorem exists_kernelRepresentation_not_exact_ck :
    exists (K : KernelRepresentation ouDiff), (forall t, ouDiff.mu.bind (K.kappa t) <= ouDiff.mu) /\
      exists s t x, K.kappa (s + t) x != (K.kappa t o_k K.kappa s) x
```
(OU triple; `K` = the Mehler kernels modified at ONE point at ONE time; it satisfies every field of `KernelRepresentation`,
is a.e.-CK, sub-invariant.)  Consequence NOT claimed: that no exact all-time semigroup exists for a given triple.
(The existence of an exact all-time semigroup representing an arbitrary compact-space `L^2` Markov semigroup is not proved and
not refuted here: it is a Kuznetsov/right-process-type statement.)

## Part (iii): non-compact Riesz-Markov for FINITE `mu`  (`R22/NonCompact.lean`)
Setting: `X` locally compact, `T2`, second countable, Borel; `mu` finite.  `C_0(X,R)` = `ZeroAtInftyContinuousMap`.
```
instance : SecondCountableTopology (OnePoint X)
theorem exists_kernel_of_posContraction_noncompact {mu : Measure X} [IsFiniteMeasure mu] (P : Lp R 2 mu ->L[R] Lp R 2 mu)
    (hpos : forall u, 0 <=^m u -> 0 <=^m P u) (hle : forall u, u <=^m 1 -> P u <=^m 1)
    (hmass : forall u, 0 <=^m u -> int (P u) dmu <= int u dmu) :
    exists kappa : Kernel X X, (forall x, kappa x univ <= 1) /\ mu.bind kappa <= mu /\
      forall (f : C_0(X,R)) (u : Lp R 2 mu), u =^m f -> P u =^m (fun x => int y, f y d(kappa x))
-- for a DiffusionTriple T on X (finite T.mu):
noncomputable def ncKernelRep (T) : KernelRepresentation T    -- all bounded measurable g in L^2, via C_c dense in L^2 (Radon mu)
theorem ncKernelRep_subInvariant (t) : T.mu.bind ((ncKernelRep T).kappa t) <= T.mu
theorem ncKernelRep_C0 (t) (f : C_0(X,R)) (u) (hu : u =^m f) : T.semigroup t u =^m fun x => int f d(kappa_t x)
theorem nc_exists_exact_ck (S : Set R>=0) (hS : S.Countable) : <the conclusion of exists_exact_ck for ncKernelRep T>
```
NOT claimed: infinite `mu` (Lebesgue/Brownian on R): the one-point-compactification reduction needs a finite
reference measure; the remaining work (weighted `L^2(h^2 mu)` with `h = R_1 g > 0`, or exhaustion by `K_n` with monotone
limits of the Riesz measures) is listed in Status.  No Feller; no all-times CK for these kernels (see (ii)).
Mass is lost at infinity allowed: `kappa_t x` is only sub-Markov (the defect is the mass sent to the point at infinity).

## DIFFERENCE FROM BGL
BGL assumes the kernel/density representation or builds it from Feller/Hunt regularity; here the representation is
constructed per fixed `t` (Riesz-Markov per `t`, a.e. identification).  BGL treats `R` with Lebesgue; here finite `mu` only.
Exact CK for all `t` is absent for the plain kernels (BGL uses Feller regularity), see (ii).

## Status
Files: `OnePointCountable.lean`, `NonCompact.lean`, `Obstruction.lean`, `AxiomCheck.lean` (only propext, Classical.choice, Quot.sound; 0 warnings; no `sorry`).

* (i): nothing new; OU/circle/Feller/zonal `S^3` bridges already hold for all `t : R>=0` (see above).  No continuity-in-`t`
  extension from countable times was proved for the plain Riesz kernels (it is exactly the Feller content).
* (ii): PROVED the obstruction `R22.exists_kernelRepresentation_not_exact_ck` (as stated; OU triple, one-point-one-time
  modification `badRep`).  NOT proved, NOT refuted: existence of some exact all-time `MarkovProcessBridge` for plain (non-Feller)
  Riesz kernels (a Kuznetsov / right-process type statement; the library's per-`t` chosen `rieszKernel` cannot supply it).
* (iii): PROVED for FINITE `mu` on locally compact, T2, second countable Borel `X` (not necessarily compact):
  `R22.secondCountableOnePoint`, `R22.exists_kernel_of_posContraction_noncompact`, `R22.ncKernel`, `R22.ncKernelRep`,
  `R22.ncKernelRep_subInvariant`, `R22.ncKernelRep_C0`, `R22.nc_exists_exact_ck`; applies to OU on `R` (example in `AxiomCheck`).
  Mathlib's `RealRMK` enters only through the compact `exists_kernel_of_posContraction` (one-point compactification, `OnePoint`).
  OPEN: infinite `mu` (Lebesgue, Brownian); the plan is `h = R_1 g > 0` a.e. (strong continuity at 0 and `P_s g >= 0`), `L^2(h^2 mu)`
  once `P_t h <= e^t h` is proved, or exhaustion `K_n` with monotone vague limits.  Representation proved on `C_0` and (by density of
  `C_c` in `L^2`) on all bounded measurable `L^2` functions; kernels are only sub-Markov (mass at infinity lost; conservativity of
  `P_t` on a non-compact space does not make the kernels Markov without a separate argument, NOT done).
* Deviations from the statement text above: statement for `ncKernelRep_*` names exactly as listed; `exists_kernel_of_posContraction_noncompact`
  additionally has `mu.bind kappa <= mu` (as listed) and uses `hmass` (as listed).  No weakening.

Proposed ERRATA rows (do not edit `ERRATA.md`):
| R22-E3-1 | INFO (scope) | Non-compact Riesz-Markov: finite `mu` only, via one-point compactification; supersedes R17-4 for finite `mu` (infinite `mu` remains open). | `Stochastic/R22/NonCompact.lean` |
| R22-E3-2 | INFO (obstruction) | `KernelRepresentation` + sub-invariance do not imply exact CK (`exists_kernelRepresentation_not_exact_ck`); so a `MarkovProcessBridge` for plain Riesz kernels is not derivable from `rieszKernel`'s API; existence of an exact all-time semigroup stays open. | `Stochastic/R22/Obstruction.lean` |
| R22-E3-3 | INFO (instance) | `OnePoint X` second countable for `X` locally compact second countable T2 (not in Mathlib at this version): `R22.secondCountableOnePoint` (a global instance in namespace `R22`). | `OnePointCountable.lean` |
Proposed `MarkovTriple.lean` imports: `MarkovTriple.Stochastic.R22.NonCompact`, `MarkovTriple.Stochastic.R22.Obstruction`, `MarkovTriple.Stochastic.R22.AxiomCheck`.
Proposed GAPS update: Round 17 item (2) non-compact: closed for finite `mu`; item (1): plain-Riesz bridge stays open, obstruction recorded.
