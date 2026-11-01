# AUDIT_HILBERT (hostile audit of `MarkovTriple/Hilbert/`)

Scope: `Hilbert/*.lean` (20 files), `Frozen/{Semigroup,MarkovTriple,FullMarkovTriple}.lean`.
Auditor files (not imported by root): `MarkovTriple/Audit/HilbertAxioms.lean`,
`MarkovTriple/Audit/HilbertDiagonal.lean`. Sources cloned shallowly (outside the project) into the
scratchpad: `src_cr/repo` (cutoff-rigidity-diffusions), `src_gp/repo` (ginibre-poincare).

## Verdict summary

| Item | Verdict |
|---|---|
| (a) `FormData`/Friedrichs, nonvacuity with `A != 0` | PASS. Nontrivial instance built and checked. |
| (b) `exists_semigroup`, `hasSpectralGap_iff_hasExpDecay` vacuous? | PASS (not vacuous). |
| (b) `isSemigroupOf_tripleSemigroup` vacuous? | NOT REFUTED, NOT CONFIRMED for `Gamma != 0`: hypothesis `IsMarkovianForm` is proved only for `Gamma = 0` (see H1). |
| (c) statements weakened vs sources | PASS. Ports are textual copies modulo namespace/imports/`DirFormData` merge. |
| (d) F5 positivity not derivable | CONSISTENT, but only argued, no counterexample constructed (see H2). |
| (e) axioms | PASS: 433 public constants, 0 offenders. |

## (e) Axioms
`lake env lean MarkovTriple/Audit/HilbertAxioms.lean` walks `env.constants` for every non-private,
non-internal constant whose module is under `MarkovTriple.Hilbert` (332 theorems, 89 defs, 12 other =
structures/ctors/recursors); result: `checked 433 constants ... offenders: []`, i.e. only
`propext, Classical.choice, Quot.sound` (no `sorryAx`, no `ofReduceBool`). Also `grep`: no `sorry`,
`axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`, `maxHeartbeats` in `Hilbert/`; only
`set_option linter.unusedSectionVars false`. (Run takes about 3 min.)

## (a) Non-vacuity with `A != 0`
`Audit/HilbertDiagonal.lean` builds `diagForm : FormData (EuclideanSpace R (Fin 2))`, `D = top`,
`A = diag(1,2)`, proving `symm`/`nonneg` from scratch, and proves (axioms: standard three only):
* `diag_A_ne_zero : diagForm.A != 0`;
* `exists_semigroup_nontrivial`: the `(P, G)` from `FormData.exists_semigroup` satisfy
  `IsSelfAdjointContractionSemigroup P`, `IsGeneratorOf G P`, and `P != fun _ => 1` (generator on
  `e0` would be `0` otherwise, contradicting `G e0 = -A e0 = -e0`);
* `semigroup_eigen0`: `diagForm.semigroup t e0 = exp(-t) e0`, i.e. `e^{-tA}` on the eigenvector
  (the eigenvalue-1 vector; second eigenvector analogous, not repeated).
Definition check of Friedrichs: closability is automatic from symmetry (`ι_injective`, proved),
`Q = range ι`, `E(u,u) = |ι^{-1}u|_K^2 - |u|^2 >= 0`, `E_emb` shows `E` restricts to `<A f, g>` on `D`;
`R = ι ι†` satisfies `R (f + A f) = f` (`R_resolvent`). This is the standard Friedrichs extension.
No density/nonnegativity-condition problem: they are exactly the fields of `FormData`.
Not tested: unbounded `A` on `l^2` (only the 2-dim bounded case); the unbounded case is exercised
only through the circle/Markov-triple bridge in principle, never by an instance.

## (b) Vacuity analysis
* `FormData.exists_semigroup` (`Existence.lean:69`): not vacuous (see (a)); it asserts
  `P` s.a. contraction semigroup, `G` s.a. closed densely defined, `G` = exact generator of `P`,
  `G <= 0`, `G` extends `-A`. It does NOT assert `P = e^{-t A_F}` or uniqueness, but pins `P`
  through `IsGeneratorOf G P` (generator characterisation is an iff), which for a strongly
  continuous semigroup determines `P`. Fine.
* `hasSpectralGap_iff_hasExpDecay` (`SpectralGap.lean:320`): hypothesis `0 <= lam` only; both sides
  are nonvacuous (lam > 0 is a genuine condition; for `lam = 0` both are true). `OrthFixed` uses
  `N = {n | R n = n} = ker G`. OK. Gap (Info): nothing connects `HasSpectralGap` to the frozen
  `PoincareIneq` (needs ergodicity: `ker G` = constants, and that `A0` is a form core), so this
  theorem is not yet usable for the frozen `PI`; this is a missing bridge, not an error.
* `isSemigroupOf_tripleSemigroup` (`Bridge.lean:138`): conclusion is the full frozen `IsSemigroupOf`
  and is proved with every conjunct except positivity unconditional. Hypothesis `IsMarkovianForm T`
  is satisfiable for `Gamma = 0` (`Sanity.lean:23`). For the circle triple
  (`Sanity/Circle.lean:371`, `Gamma = f' g'`, trig polynomials) it is mathematically true (closure of
  trig polynomials is `H^1(T)`, a Dirichlet form) and the hypotheses of
  `isMarkovianForm_of_approx` hold mathematically (Fejer means `sigma_N |f|` are trig polynomials,
  `sigma_N` is a contraction on `H^1`, `sigma_N|f| -> |f|` in `L^2`, `|f|` Lipschitz so
  `|| (|f|)' ||_2 <= || f' ||_2`). I did NOT machine-check this: it needs Fejer-kernel
  convergence in `H^1`, absent from Mathlib (est. 300-500 lines). So non-vacuity of the bridge for
  `Gamma != 0` is unproved. See H1.
  Sanity note: in finite discrete spaces any Markov triple has `Gamma = 0` (choose `psi` with
  prescribed value and zero derivative at a point), so no finite-space test of `Gamma != 0` exists;
  the circle is the minimal test.

## (c) Statements vs sources
Normalised diff (leading whitespace stripped) of ported files against sources:
`DiffFriedrichs->Friedrichs`, `DiffCfcSemigroup->CfcSemigroup`, `DiffFrResolvent->Resolvent`,
`DiffFrComplex->Complexify` (and `DiffFrDeriv`, `DiffFrPow`): differences are only `module`/`public
import`/`@[expose]`/namespace lines. `DiffMarkov -> DirMerge`: only `DirFormData -> FormData` rename;
`DirFormData` was a verbatim field-for-field mirror of `FormData` (checked: same 5 fields), so the
merge is sound. `GeneratorCompletion -> OperatorSquareCompletion`: namespace/import only. No
weakening found. The NEW statements (`exists_semigroup`, spectral gap, Bridge, Closure,
MarkovCriterion) have no source; they are judged above. `IsMarkovianForm` is the first
Beurling-Deny criterion exactly as used (`|u| in Q`, `E(|u|) <= E(u)`); the cone argument in
`BeurlingDeny.lean` (pair `<g, |u|-u> >= 0` for `g >= 0`, fixed points of `|.|` are `>= 0`) is the
standard proof and is axiom-clean.

## (d) F5: positivity is not derivable from the fields
Why it should not be derivable: positivity of the Friedrichs semigroup is equivalent (Beurling-Deny)
to `u in Q => |u| in Q, E(|u|) <= E(u)` for the *closure* of the pre-form on `A0`. The fields give
the chain rule only for `psi(f) in A0`; BGL Def 3.1.8 additionally has `A0` stable under smooth
`psi`, which gives `psi_eps(f) in A0` and hence Markov. `Frozen/MarkovTriple.lean:67`
(`diffusion`, "whenever `psi(f) in A0`") and the docstring's declared deviation drop exactly this.
Without stability the only information about the closure is its core; the only tool is closure of
`Gamma`-bilinear data, which cannot see `|f|`.
I could NOT construct a counterexample triple (a triple satisfying all frozen fields with a
non-Markovian Friedrichs form). Attempts: (i) finite/discrete: forces `Gamma = 0`, trivially Markov;
(ii) genuine differential operators on algebras (trig polynomials, OU polynomials): Markov;
(iii) boundary-type algebras (Robin-like conditions) are not algebras (`(fg)' = 2c fg != c fg`).
Candidate class worth investigating (not verified): `E = R`, `Gamma = a f'g'`, `A0` = polynomials, `mu`
an N-extremal indeterminate Hamburger measure (polynomials dense in `L^2` but the closure of the
polynomial form in `H^1(mu)` may be a non-Markov Friedrichs/Krein-type extension). So: F5 claim
"cannot be derived from the structure fields" is plausible and consistent with the literature, but is
an unproved non-derivability claim. Do not describe it as refuted-by-counterexample.

## Findings

### H1 (Medium) `Bridge.lean:138`, `Sanity.lean:23`: bridge nonvacuity only for `Gamma = 0`
The only machine-checked instance of `isSemigroupOf_tripleSemigroup` has `Gamma = 0`, `L = 0`. A
bug in `IsMarkovianForm` making it false whenever `Gamma != 0` would go unnoticed. I found no such
bug by reading, and the circle satisfies it mathematically.
Fix: prove `isMarkovianForm_of_approx` hypotheses for `circleTriple` (Fejer means in `H^1`; or use
Mathlib's `fourier` L^2 partial sums `S_N` together with `energy(S_N h) = sum_{|k|<=N} k^2 |h_k|^2 <=
energy(h)` for `h = |f|` via its Fourier coefficients), giving `circleTriple_friedrichs_isSemigroupOf`.

### H2 (Medium, design) `Frozen/MarkovTriple.lean:67`, `Frozen/Semigroup.lean:15-20`: Markov property is not in the structure
Because `A0` is not required to be `psi`-stable, `IsSemigroupOf` (which demands positivity) may have
NO witness for some triples; then every theorem of the form `forall P, IsSemigroupOf T P -> ...`
(including `FullMarkovTriple.semigroup_stable`, `Frozen/FullMarkovTriple.lean:61`) is vacuous for
that triple. Downstream (CD/LSI via semigroup interpolation) must carry `IsMarkovianForm T`
explicitly.
Fix: either add a field to `FullMarkovTriple` asserting (an unfolded form of) `IsMarkovianForm`
(e.g. `forall f in A0, forall eps > 0, exists g in A0, |g - |f||_2 < eps and E(g) <= E(f)+eps`, which is
exactly the hypothesis of `isMarkovianForm_of_approx` and is checkable for circle/OU), or
state all semigroup-using theorems with `(hM : IsMarkovianForm T)`. Frozen files are not edited here.

### L1 (Low) `Frozen/Semigroup.lean:20`: uniqueness claim unproved
Docstring: "When `L|A0` is essentially self-adjoint such a `P` is unique". Not proved anywhere
(`Closure.lean` header and HILBERT_STATUS admit this). Mathematically true (generator of a symmetric
strongly continuous semigroup is s.a. and extends `L|A0`, so equals the unique s.a. extension), but
the field `semigroup_stable` quantifies over all `P`, so uniqueness is what makes the Friedrichs
witness the only relevant one.
Fix: prove `FullMarkovTriple.isSemigroupOf_unique` (needs: strongly continuous symmetric
semigroup => generator s.a.), or weaken the docstring to "expected unique".

### L2 (Low) `Hilbert/Existence.lean:69`: no identification `P = e^{-tA}` stated
`exists_semigroup` gives `P` only via its generator. Adequate, but a user must go through
`tendsto_generator_iff`. Optional: add `semigroup_eigen`-type corollary (I proved the eigenvector
case in `HilbertDiagonal.lean`).

### I1 (Info) `SpectralGap.lean:73`: `HasSpectralGap` is not `PoincareIneq`
No lemma links them (ergodicity + core/closure). Needed for F1-style statements.

### I2 (Info) real-only Hilbert layer
`FormData` is for real Hilbert spaces; complex CFC is internal (`Complexify.lean`). Fine for L^2(mu;R).

## Per-file verdicts
Friedrichs OK; Complexify, CfcSemigroup, SemigroupDeriv, SemigroupSmoothing, Resolvent,
ResolventGenerator OK (textual ports, axiom-clean); Generator OK (new, iff characterisation);
Existence OK (L2); SpectralGap OK (I1); BeurlingDeny OK; DirMerge, DirBridge OK;
TripleForm OK (well-definedness of `A[f] = -[Lf]` proved via Cauchy-Schwarz, density used correctly);
Bridge OK modulo H1/H2; MarkovCriterion OK modulo H1; Closure OK (L1); Sanity weak (H1);
OperatorSquareCompletion OK (namespace-only port); AxiomCheck OK (superseded by Audit/HilbertAxioms).
Frozen/Semigroup.lean: L1. Frozen/MarkovTriple.lean: H2. Frozen/FullMarkovTriple.lean: H2 (vacuity of
`semigroup_stable`).
