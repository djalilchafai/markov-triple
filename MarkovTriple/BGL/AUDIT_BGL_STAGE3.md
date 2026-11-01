# AUDIT BGL STAGE 3 (round 8, hostile, Armstrong method)

Scope: BGL/Semigroup/*, BGL/Calculus/*, BGL/Instances/Circle/*, BGL/Instances/OU/{Diffusion,Semigroup,Full},
BGL/Theory/* (not Compact), BGL/Frozen/* (context).  Excluded: Instances/Lebesgue, Theory/Compact, OU/LSI*.
New files only: `BGL/Audit/Stage3Probes.lean`, `BGL/Audit/Stage3Walk.lean` (not imported by root; `lake build
--no-build` reports all targets up to date).  Book used only as paraphrase (BGL Thm 4.8.4: P(C), C = (n-1)/(rho n)).

## Verdict per component

| Component | Verdict |
|---|---|
| Semigroup/* (positivity, sub-Markov, conservative transfer, Mass, ESA, Characterization) | PASS. All statements are about a bare `DiffusionTriple` (variables `T : DiffusionTriple E`, plus `[IsFiniteMeasure T.μ]` only in section `Finite`, `S : StandardTriple` only in `StandardTriple` namespace theorems). No smuggled hypothesis found. |
| Calculus/* (fundamental identity, chain rule, density, LSIExtend) | PASS. `fundamental_identity_ae` checked by hand on Gamma = f'g' (both sides 2f'^2 g + 2 f f' g'); hypotheses only `f g in A0`. |
| Circle (`circleCompact`) | PASS. Genuine: `A0 = C^infty(T)` via smoothness of `t -> f (t:T)`, `D f = deriv (t -> f(x+t)) 0` (no junk, f smooth), S10 by Fourier coefficients, S11 by mode 0, F8 by `smoothing` + `semigroup_mc` (eigenvalue e^{-(2 pi n)^2 t}), F10 via `core_of_invariant`, `Gamma != 0` proved. `circle_CD` is on all of `A` for `rho <= 0`, `n in [1,inf]` (correct: Gamma2 = (f'')^2, so rho > 0 is false). |
| OU (`ouFull`) | PASS. `A0 = C_c^infty`, `A = C^infty` (`Afull`, `Sm f`), `L f = f'' - x f'`, `Gamma = f' g'`, mu = gaussianReal 0 1; semigroup pinned by `Pt_hL` (Hermite eigenvalues e^{-nt}) and Mehler, so it is the Friedrichs semigroup, not trivial. S10/S11/F10 are real theorems (via ESA, Hermite). `ouFull_CD : CD 1 inf` on all of `A`, correct (Gamma2 = f''^2 + f'^2); finite `n` is (rightly) not claimed. |
| Theory unconditional (`poincare_of_CD_infty`, `poincare_of_CD_dim`, `conservative_of_esa`, Gamma2Integral, ALevel, GammaCalculus, Convergence) | PASS. Constants correct: PI(1/rho) and PI((1-1/n)/rho) = PI((n-1)/(rho n)); derivation `rho' = rho/(1-c)` from integrated CD is right and matches the book's proof. Lichnerowicz sharp (OU: equality for f = x, limit of C_c^infty). `hn : 1 < n` is necessary and correctly stated (n = 1, rho > 0 would give C = 0). |
| Theory conditional (`GradientInterpolation`, `EntropyInterpolation`, `gradient_bound`, `ent_le_fisher`, `logSobolev_of_CD_infty`) | PASS with caveat C1. Conclusions follow with no hidden assumptions (CD used only for `Gamma2 - rho Gamma >= 0` plus nonnegative `n^{-1}(Lg)^2`; monotonicity of `e^{-2 rho s} Phi(s)` verified; weak gradient bound is in the book; LS(1/rho,0) is `Ent(f^2) <= (2/rho) E(f)`, correct). |
| Frozen-surface protection (`scripts/check_frozen.py`) | PASS with caveat C3. |
| Axioms / banned constructs | PASS. |

## Findings

### C1 (LOW/INFO) The conditional hypotheses are machine-checked satisfiable only for the one-point triple
`Theory/Tests.lean` proves `GradientInterpolation`/`EntropyInterpolation` for `trivialCompact` (Gamma = L = 0), where every
field is `HasDerivAt _ 0`.  That excludes only gross contradictions.  I looked for a hidden inconsistency for OU / circle and
found none:
* representatives: `Pt` uses `Classical.choose`, but on OU and the circle `A = C^infty` and the measure has full support,
  so the representative is unique (a.e.-equal continuous functions are equal); moreover `ALevel` proves `L`, `Gamma` depend only on
  a.e.-classes on `A`.  No junk.
* every `Integrable` clause is explicit (no Bochner junk); `0 <= phi <= M` gives `g_s in [eps, eps+M]` everywhere, so `Lambda o g_s = log g_s`.
* `Phi' = 2 int k_s Gamma2(g_s)` (sign/factor re-derived: d/ds int P_s h Gamma(P_{t-s}f) = int P_s h (L Gamma(g) - 2 Gamma(g,Lg)));
  `e' = -I` and `I' = -2J` are the standard de Bruijn identities.  On OU all integrands are bounded or Gaussian-integrable for
  `f,h in C_c^infty`; so the structures are mathematically true there.
Not machine-verified.  Fix (optional): prove `GradientInterpolation circleFull` (compact, graph-norm differentiation) as a
non-degenerate witness.
Also: `poincare_of_CD_dim` (finite n, rho > 0) and the LSI have no non-degenerate instance among the audited files
(circle needs rho <= 0, OU only n = inf); only the one-point triple witnesses non-vacuity (Lebesgue/Compact agents may add).

### C2 (LOW, doc) wrong file reference
`BGL/Theory/ESAOne.lean:14` says "see `Theory/Conservative.lean`"; the file is `BGL/Semigroup/Conservative.lean`
(GAPS.md G4 mentions completeness but the same dangling name appears in the docstring only).  Fix the docstring.

### C3 (LOW) `check_frozen.py` robustness (tested on a COPY in the scratchpad)
Tests (copy at `<scratchpad>/cp`):
* append a line to a fenced file (`Hilbert/Friedrichs.lean`) -> `CHANGED (fenced)`, FAILED.  caught
* append to a frozen file (`BGL/Frozen/CD.lean`) -> `CHANGED ... (status proposed)`, FAILED.  caught
* frozen file imports `BGL.Semigroup.Mass` -> CHANGED + `UNFENCED Hilbert/SubMarkov.lean`, `TripleForm.lean`.  caught
* fenced file `Hilbert/Existence.lean` gains `import MarkovTriple.BGL.Semigroup.Mass`, manifest `--update`d ->
  `UNFENCED MarkovTriple/Hilbert/{MarkovCriterion,SubMarkov,TripleForm}.lean`, FAILED.  caught (closure check works)
* same with `import all MarkovTriple.BGL.Semigroup.Mass` or `import Mathlib MarkovTriple.BGL.Semigroup.Mass` (after `--update`) ->
  prints OK.  NOT caught: the import regex `import\s+(MarkovTriple\.\S+)` only matches a plain single-module import at line
  start (misses `import all X`, `public import X`, `meta import X`, several modules on one line).
  No such import exists in the repo today (grep), so no current hole.  Fix: parse tokens after `import`/`import all`/`public import`.
* Not hashed: `frozen-manifest.json`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` (a Mathlib bump would silently change
  the meaning of `Lp`, `variance`, `gaussianReal` used in frozen statements); `--update` is unguarded (by design: "drafter only").
  New `.lean` under `Frozen/` is caught (`UNLISTED`).

### C4 (INFO) coverage of the axiom walk
`Audit/Stage3Walk.lean` walks every non-internal constant whose defining module lies in Semigroup, Calculus, Theory (except
Compact), Instances.Circle, Instances.OU (except LSI), Frozen, Sanity, Audit: 425 constants, 0 extra axioms, 0 `sorry`
terms, 0 unsafe/partial, 0 declared axioms (run time about 2 min).  `_private`/`match_`/`proof_` names are skipped by
`isInternal` but are covered through `collectAxioms` of their public users.  Grep over BGL (excluding Lebesgue, Compact, OU/LSI)
for `sorry|axiom|native_decide|unsafe|opaque|implemented_by|extern|partial|admit`: only the English words "partial derivative"
in `Frozen/PartialDeriv.lean`; no `set_option` other than linter ones.

## Probes in Lean (BGL/Audit/Stage3Probes.lean; axioms: propext, Classical.choice, Quot.sound)
* `gaussian_poincare`: from `FullTriple.poincare_of_CD_infty ouFull one_pos ouFull_CD`, unfolded to the concrete statement
  `f : R -> R`, `ContDiff R top f`, `HasCompactSupport f` implies
  `variance f (gaussianReal 0 1) <= int (deriv f x)^2 d(gaussianReal 0 1)`  (Gaussian Poincare PI(1)).  Compiles.
* `ou_conservative_via_esa`: `DiffusionTriple.conservative_of_esa ouDiff (ou_esa_core) expo t` gives S11 for the explicit
  exhaustion `expo` without using the `conservative` field.  Compiles.
* `semigroup_one2` applied to `circleCompact` (finite measure, `esaProp`): compiles.

## Not found (refutation attempts that failed)
Vacuous/empty-class tricks (PI on `A0`, nonempty, dense); Bochner junk in S10/S11/F2/CD/PI statements; circular S11 (derived
from ESA + D8 only, then compared with the frozen field); `esa_auto` is proved from F8 independently of the `esa` field;
nonnegative-only S11 field is upgraded to all exhaustions by `conservative_all` (needs positivity/sub-Markov, both theorems).
