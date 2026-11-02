# Hostile audit R2 of the BGL frozen surface (`MarkovTriple/BGL/Frozen/*.lean`, 17 files)

Method: Lean files read in full (536 lines); book text (Defs 3.1.1, 3.1.3, 3.1.8, 3.1.10-3.1.12, 3.3.1, 3.3.7,
3.3.14, 3.3.25-26, summary 3.4.1-3.4.4, 4.2.1, 5.1.1, (5.1.1), (5.1.6), Sect. 1.14 "good measure space") read
directly; prior audits (`AUDIT_BGL_SURFACE.md`, `FROZEN_REVIEW_BGL.md`) read only AFTER forming my own list, then
used to avoid repeating items.  Instances (circle, Lebesgue, OU, `Sanity/Trivial`) read for non-vacuity.
Machine checks run: `lake env lean` probe (coercion `(⊤ : ℕ∞) : WithTop ℕ∞` = C^∞, not analytic: OK;
`#print axioms FullTriple.CD` = propext/choice/Quot.sound).  `grep sorry/axiom/native_decide` over
`MarkovTriple/` outside `BGL/Audit` and docstrings: no hit.  `frozen-manifest.json` now lists `BGL/FormData.lean`,
`BGL/Basic.lean` and the `Hilbert/*` files, so prior finding M1 (meaning-bearing definitions outside the hash
perimeter) is RESOLVED.

## Verdict

No CRITICAL or HIGH finding.  I could not build an inconsistent or trivially-satisfiable-by-junk model, and I could
not refute any field's faithfulness to the book.  Real residual issues: one MEDIUM (D1 "good measurable space"
dropped, with a concrete non-good counter-model), and a handful of LOW items (generic PI/LS/Ent/Fisher/energy
defs that carry junk values and vacuity when used outside their intended guards; typeclass ergonomics;
documentation points).  Details and fixes follow.  A "tried and failed" list (attacks that did NOT succeed) is
at the end, because it is part of the evidence.

## Findings, severity-ranked

### M1 (MEDIUM) D1 "good measurable space" is not encoded: the structure admits non-separable `L²(μ)`

`Frozen/DiffusionTriple.lean` docstring says it is NOT encoded and "no hypothesis uses it".  Book (Def. 3.1.1, D1,
Sect. 1.14): `(E,F,μ)` good = countable family generating `F` up to μ-null sets, and measure decomposition and
bi-measure theorems apply.  Consequences in the book: all `L^p`, `1 ≤ p < ∞`, are separable; kernel representation
(Prop. 1.2.3, (3.1.14)), disintegration.

Concrete counter-model (sketch, not formalised): `E = 𝕋^I` with `I` uncountable, product σ-algebra, Haar
probability `μ`, `𝒜₀ = 𝒜 =` smooth cylinder functions (bounded, algebra, stable under smooth ψ, dense in all `L^p`),
`Γ(f,g) = Σ_i ∂_i f ∂_i g`, `L f = Σ_i ∂_i² f` (finite sums on cylinders).  D1-D8, S10 (kernel = constants),
S11, F1-F10 hold coordinatewise exactly as for the circle (`Instances/Circle`), ESA because Fourier characters (finite
products) form a core.  But `L²(𝕋^I)` is non-separable, so the σ-algebra is not countably generated mod null sets: the
triple satisfies every Lean field and is not a BGL triple.  Likewise (non-Polish measurable spaces) anything where the
decomposition theorem fails.

Impact: every theorem already proved is sound (weaker hypotheses).  Risk is downstream fidelity only: any later
formalisation of the semigroup kernel `p_t(x,dy)`, of the spectral resolution with a countable family, of
Markov-process / path-space statements, or of results quoted from Ch. 1 that need good spaces will not be derivable, or
worse, will be "proved" under an extra hypothesis added ad hoc.  The three instances are all standard Borel.

Fix (additive, not editing frozen text in place): either add a field, or (preferred, as it keeps the existing
`DiffusionTriple` terms unchanged) a Prop-valued predicate bundled in a refined structure:
```lean
/-- Sect. 1.14: countable generation of the σ-algebra up to `μ`-null sets (equivalently, for σ-finite `μ`,
separability of `L²(μ)`), the checkable half of "good measure space". -/
def IsGoodMeasure {E : Type*} [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∃ 𝒢 : Set (Set E), 𝒢.Countable ∧ (∀ s ∈ 𝒢, MeasurableSet s) ∧
    ∀ s, MeasurableSet s → ∃ t, MeasurableSet[MeasurableSpace.generateFrom 𝒢] t ∧ μ (symmDiff s t) = 0
-- minimal usable consequence (to be proved as a lemma, then used instead of a field):
-- IsGoodMeasure μ → [SigmaFinite μ] → TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)

structure GoodDiffusionTriple (E : Type*) [MeasurableSpace E] extends DiffusionTriple E where
  good : IsGoodMeasure μ
```
The measure-decomposition half is naturally taken from `StandardBorelSpace E` (or an a.e.-isomorphic standard Borel
model); do not try to state it abstractly.  For the three instances: `IsGoodMeasure` is immediate from Borel σ-algebra
on a second-countable space (take `𝒢` = countable basis).

### L1 (LOW) Generic `PoincareIneq` / `LogSobolevIneq` / `energy` / `Ent` / `fisherInfo` are public, unbound and carry junk

(Prior M2 recorded this; status: the triple-bound `DiffusionTriple.PI/LS` and the extension theorems
`PI.extend`, `LS.extend` now exist, so the severity is down to LOW.  The generic definitions remain frozen and
public, so the hazards remain for new code.)
* `PoincareIneq μ Γ ∅ C` and `LogSobolevIneq μ Γ ∅ C D` are true for every probability μ, every Γ (probes in
  `Audit/Probes.lean`).  A statement of the form `PoincareIneq μ Γ 𝒞 C` with `𝒞` not provably dense in
  `formDomain` is therefore not the book's P(C).
* `Real.log` is `log |·|`, so `Ent μ f` for `f` taking negative values is not an entropy; `Ent` has no
  integrability guard (junk `0` for `∫ f log f` non-integrable, and `∫ f = 0` junk if `f ∉ L¹`; the book's (5.1.1)
  is for "positive integrable f with ∫ f |log f| < ∞", for arbitrary σ-finite ν).  With μ infinite, `f ∈ L¹`-failure
  gives `Ent` = junk.  In `LogSobolevIneq` the argument is `f²` (nonneg) on bounded `A₀`: safe.
* `fisherInfo` has `x / 0 = 0` junk; `IsFisherAdmissible` is the right guard but is not a hypothesis of `fisherInfo`.
Fix: add a guard predicate next to `Ent` and make downstream theorems take it:
```lean
def IsEntAdmissible (μ : Measure E) (f : E → ℝ) : Prop :=
  (0 ≤ᵐ[μ] f) ∧ Integrable f μ ∧ Integrable (fun x => f x * Real.log (f x)) μ
```
and add to the docstring of `PoincareIneq`/`LogSobolevIneq` "use only through `DiffusionTriple.PI/LS`, or with a `𝒞` for
which a density lemma into `formDomain` exists".

### L2 (LOW) Typeclass ergonomics: `sigmaFinite`, `finite_prob` are fields, not instances

`DiffusionTriple.sigmaFinite : SigmaFinite μ` and `finite_prob` are structure fields whose types are classes but they are
not registered as instances (only `Theory/Compact/Entropy.lean` makes a local `instProb`).  Every user must write
`haveI := T.sigmaFinite`.  Not a soundness issue; the risk is someone adding a *different* instance
(e.g. `IsProbabilityMeasure T.μ` from a context hypothesis) that is not definitionally the field.  Fix, outside
Frozen: `instance (T : DiffusionTriple E) : SigmaFinite T.μ := T.sigmaFinite`; and
`theorem DiffusionTriple.isProb_of_finite (T) [IsFiniteMeasure T.μ] : IsProbabilityMeasure T.μ := T.finite_prob ‹_›`.

### L3 (LOW) CD is stated only for `FullTriple`; `Γ₂` and `CD` are meaningful only on `A`

`Frozen/Gamma2.lean`: `Γ₂ f g` applies the *total* function `L` to `ΓA f g` and `ΓA` to `L f`; for `f ∉ 𝒜` this is
junk (arbitrary values of the total function `L`).  The book's Γ₂ is `A × A → A` (checked: `ΓA f g ∈ A` and
`L f ∈ A` for `f, g ∈ A` are derivable, so on `A` it is well defined, and `L` is class-invariant on `A` via F7 + F2).
`CD` quantifies only `f ∈ T.A`: correct.  Book Def. 3.3.14 is also given for Standard triples via `A₀`
(Remark 3.3.15 extends to `A` using ideal + F2 + F6) and that form cannot be stated for `StandardTriple`.  Not a
defect for Full/Compact triples (what every theorem of Ch. 3.3+ assumes); document it, and if a
`StandardTriple`-level CD is ever needed add `CD₀ : ∀ f ∈ A₀, …` (ΓA/Γ₂ formulas already make sense; `ΓA f f ∈ A₀`
for `f ∈ A₀`).
Check of conventions: `n : ℝ≥0∞`, `1 ≤ n ∧ …`: n < 1 excluded (as in the book, `n ∈ [1, ∞]`), `(n⁻¹).toReal`
with `1 ≤ n` has no junk, `⊤⁻¹ = 0` gives CD(ρ,∞).  `¬ CD ρ 0` proved in `Sanity/Trivial`.  Note CD is a *conjunction*
`1 ≤ n ∧ …`, so `¬ CD ρ n` is not "curvature fails" for `n < 1`; harmless but state this when quoting negative results.

### L4 (LOW) Documentation-level deviations (confirmed faithful, but make explicit)

* `CompactTriple`: `A = A₀` together with `Subalgebra` (unital, contains constants) forces `1 ∈ 𝒜₀ ⊂ L¹`, hence
  `μ` finite (hence probability) and `𝒜₀` unital; consistent with the book's compact case (compact manifolds), not
  stated anywhere in the frozen docstring.  ESA is kept as a (redundant) field; `esa_auto` proves it.
* D4 and the second form of S10 (`f ∈ 𝒟(ℰ)`, `Γ(f)=0 ⇒` const) are not fields; theorems `exists_bound_D4` and
  `StandardTriple.energy_zero_const` exist.  Fine.
* `IsExhaustion` increasing a.e. (class reading); `exhaustion` is a pure existence field, `S11` quantifies over ALL
  nonnegative exhaustion sequences.  Non-vacuity of `S11` rests on `DiffusionTriple.exists_nonneg_exhaustion`
  (`Semigroup/Conservative.lean:220`, proved) and the equivalence on `conservative_all` (proved).  Keep both in
  `AxiomCheck.lean`.

## Field-by-field verdicts (own reading, against the book)

| Item | Verdict |
|---|---|
| D1 | σ-finite + prob-if-finite: faithful; "good" missing (M1). `finite_prob` kills `μ = 0` and hence empty `E` (checked by hand: on `Empty`, `μ = 0` is finite, so would need prob, contradiction). |
| D2 | bounded everywhere, algebra, dense in all `L^p` (`dense` with `Fact (1 ≤ p)`, `p ≠ ∞`), `memLp` (implicit in "dense in `L^p`" and needed for infinite μ), `comp_mem` for all k, smooth ψ, ψ(0)=0 (k=0 gives only `0`). Faithful. `ContDiff ℝ (⊤:ℕ∞)` = C^∞ (probed). |
| D3 | `Γ_mem`, symmetry/additivity/homogeneity (first variable; second by a.e. symmetry), `Γ_nonneg`, diffusion for all k, ψ smooth, ψ(0)=0, equality a.e. Faithful. Fundamental identity (3.1.1) derivable (ψ(x,y)=xy). |
| D4 | theorem, not field (Cauchy–Schwarz from D5, D6). OK. |
| D5, D6, D8 | `ibp`, `L_mem`, `integral_L`: no junk (every integrand in `𝒜₀ ⊂ L¹`). `L f` unique a.e. by density; `L` is class-invariant on `𝒜₀` (from ibp + symmetry). D8 is independent of D5 because `1 ∉ 𝒜₀` (non-unital). OK. |
| D7, D9 | `formDomain`, `closedForm`, `generator`, `semigroup` via Friedrichs `formData` (now in manifest). `generator` domain = book's `{f ∈ 𝒟(ℰ): |ℰ(f,g)| ≤ C‖g‖}`. OK. |
| S10 | `u ∈ 𝒟(L)`, `L u = 0 ⇒ ∃ c, u =ᵐ c`. For infinite μ forces `c = 0` since `u ∈ L²`. Faithful. |
| S11 | exhaustion formulation, see L4; equivalent to `P_t 1 = 1` for finite μ (positivity ⇒ monotone) and the right meaning for infinite μ. Neither too weak (kills killed BM on (0,1): `P_t u_n → P_t 1 < 1`) nor too strong (satisfied by circle, ℝ, OU). |
| F1 | literal `h * f ∈ 𝒜₀`. OK |
| F2 | premise over `0 ≤ᵐ h`, conclusion `0 ≤ᵐ f`. The a.e. reading is the faithful *class* reading (book's `𝒜₀` consists of classes); a pointwise-positive `h` would be a (slightly) stronger axiom than the book's. `∫ h f` is a genuine integral (`h f ∈ 𝒜₀ ⊂ L¹` by F1). |
| F3-F6 | `A_comp` (all smooth ψ, no ψ(0)=0), `L_mem_A`, `ΓA_nonneg`, both change-of-variables formulas with `pderiv₂ ψ i j = ∂_j∂_iψ`, all a.e. Faithful. Γ on `𝒜` is the formula (F4) by construction. `ΓA = Γ` a.e. on `𝒜₀` (derived, checked by hand via ibp, ψ(x,y)=xy, density). |
| F7 | both equalities, all three integrals genuine (`g Lf`, `f Lg`: ideal; `L(fg)`: `fg ∈ 𝒜₀`). OK. |
| F8 | `∃ g ∈ 𝒜` representing `P_t [f]`. Faithful (the book's `P_t f` is a class). |
| F9 | `ΓA f f =ᵐ 0 ⇒ f =ᵐ const`. Faithful. |
| F10 | "∀ u ∈ 𝒟(L) ∃ a_n ∈ 𝒜₀, a_n → u, L a_n → L u": `𝒜₀` is a core of the Friedrichs generator `G`. ESA ⇔ `cl(L|𝒜₀)` self-adjoint ⇔ `cl(L|𝒜₀) = G` (G is a self-adjoint extension) ⇔ core. Equivalent to the book's `𝒟(L) = 𝒟(L*)`. |
| CD | see L3. |
| PI, LS | triple-bound versions on `𝒜₀` match Defs 4.2.1 / 5.1.1 (`Var ≤ Cℰ`, `Ent(f²) ≤ 2Cℰ(f) + D∫f²`, `C > 0`, `D ≥ 0`, probability measure); extension to `𝒟(ℰ)` proved (`PI.extend`, `LS.extend`; for LS, Fatou on `f² log f² ≥ -1/e` is what makes extension valid). Generic versions: L1. |
| Ent, Fisher | formulas match (5.1.1), (5.1.6); guards: L1. |

## Non-vacuity of the existing instances (fields actually used, not just sketched)

`Circle.circleCompact`, `OU.ouFull`, `Lebesgue.Full` are fully proved in Lean (no sorry), with `Γ ≠ 0`
(`circleCompact_Γ_ne_zero`, `ouFull_Γ_ne_zero`).  I read `Circle/Triple.lean` and `OU/Full.lean` field by field:
every field is discharged by a genuine argument, none by a junk coincidence.  Points I specifically checked:
* `exhaustion`: circle: finite μ so constants; OU: `expo` cutoffs (monotone, compact support), Lebesgue: cutoffs; so
  `1 ∈ 𝒜₀` is not needed.
* `pos_detect`: circle by `ae_nonneg_of_pairing`, OU by a bump-function argument using `OpenPosMeasure`; they use
  only a.e.-nonnegative test functions in the premise, consistent with the Lean F2.
* `ibp_A`, F7: real integration by parts (compact support / periodicity), not `0 = 0` (integrability is automatic).
* `esa` for circle via `core_of_invariant` (needs F8-type invariance, real content); OU via `ou_esa_core`.
* S11 for OU/ℝ is the exhaustion statement with a genuinely infinite-ish (ℝ, Lebesgue) case checked in Lebesgue.
* `Sanity/Trivial.trivialCompact` is on `Unit`: shows consistency but is degenerate (Γ = 0), so it is no evidence for
  non-vacuity of S10/F9 or CD with positive curvature; the circle/OU/Lebesgue instances are.
No instance exercises: `n` finite and `> 1` in CD with `ρ > 0` (circle: `ρ ≤ 0`; OU: `CD(1,∞)` only).  Suggested extra
non-vacuity witness, to make the `n < ∞` branch non-degenerate: sphere `S^n` or `CD(ρ, n)` for OU with `n = ∞` only is
already covered; the circle satisfies `CD(0, 1)` exactly (`Γ₂(f) = (f'')² = (Lf)²`) which exercises `(n⁻¹).toReal = 1`.

## Attacks that failed (kept as evidence)

1. Inconsistency by degenerate triples: empty `E`, `μ = 0`, `𝒜₀ = {0}` (needs `L^p = 0`, so μ = 0, excluded by
   `finite_prob` unless μ infinite-and-zero, impossible since σ-finite zero measure is finite).  Excluded.
2. Trivial `Γ = L = 0` on a space with ≥ 2 atoms or non-atomic μ: not ergodic (S10 forces `L²(μ)` one-dimensional,
   i.e. a single atom).  Only `Unit` survives; fine, the book allows it.
3. "Satisfied by junk": the integrals in D5, D8, F2, F7 are over `𝒜₀ ⊂ L¹`; no Bochner `0` coincidences.  `ENNReal.toReal`
   only on `(n⁻¹)` with `n ≥ 1`.  `pderiv` junk only where ψ is not differentiable (never, ψ smooth).
4. Literal membership (`Γ f g ∈ 𝒜₀`, `L f ∈ 𝒜₀`, `ideal`) vs the book's class reading: strengthens nothing, since `L`
   and `Γ` are total functions chosen by `Classical.choice` among representatives; a model exists iff the class-level
   statement holds (class invariance of `L` on `𝒜₀`, `𝒜` follows from ibp/F7 + density/F2).
5. `L` on `𝒜` not class-invariant: false, F7 + F1 + F2 give `L g =ᵐ L g'` when `g =ᵐ g'` in `𝒜`.
6. S11 stronger/weaker than `P_t 1 = 1`: shown equivalent (positivity of `P_t`, `conservative_all`); fails for killed BM
   as it should.
7. F10 weaker/stronger than ESA: equivalent (core of the Friedrichs extension); fails for `C_c^∞(0,1)` Dirichlet
   Laplacian (as it should), holds for circle/ℝ/OU.
8. CD with `n < 1`, `n = ∞`, `ρ` any real: handled (n<1 excluded; `⊤⁻¹ = 0`).
9. Universe/typeclass: `E : Type*` throughout, `Lp ℝ p μ` instances found; no universe issue.  (L2 only ergonomics.)
10. `finite_prob` vs `CompactTriple`: consistent (compact ⇒ finite).

## Recommended actions (priority)

1. M1: add `IsGoodMeasure` (+ lemma `separable_Lp`) and a refined structure or field; discharge for the three
   instances.  Do not touch frozen text until a decision on whether D1-good is wanted as a field or a wrapper.
2. L1: add `IsEntAdmissible`; restrict public use of generic `PoincareIneq`/`LogSobolevIneq` to the triple-bound
   versions in docs.
3. L2: register `SigmaFinite T.μ` instance and the finite-probability corollary (outside Frozen).
4. L3/L4: docstring remarks only.
