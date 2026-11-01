# FROZEN_REVIEW: frozen definition surface (status: all `proposed`; REDESIGNED in round 2)

Files: `MarkovTriple/Frozen/{PartialDeriv,MarkovTriple,Gamma2,CD,Energy,Ent,Poincare,LSI,Fisher,Semigroup,FullMarkovTriple}.lean`.
Sanity (not frozen): `MarkovTriple/Sanity/Trivial.lean`. Manifest: `frozen-manifest.json`; check with `scripts/check_frozen.py`.
BGL numbering in docstrings is partly from memory; entries marked "numbering to be verified" must be checked against the book.
`Frozen/Basic.lean` (old placeholder) was deleted (ERRATA E1). Files now also include `Ergodic`, `CDFull`.

## Round 2 redesign (DECISIONS 8–11): what changed vs the Phase-2 text below

Items 2, 4, 6 and 12 below describe the superseded Phase-2 design; this section is binding.
All BGL numbering below ("§3.1", "Def. 3.1.x", "§3.3–3.4") is UNVERIFIED against the book (DECISIONS 11).

R1. **μ σ-finite, not finite.** `A₀ : NonUnitalSubalgebra ℝ (E → ℝ)`; constants no longer in `A₀`
   (so `1 ∈ Lᵖ` no longer forces `μ` finite). `sigmaFinite` stays a field. Witness: `Sanity/Lebesgue.lean`
   (`volume` on ℝ, `lebesgueTriple_not_finite : μ univ = ∞`).
R2. **`comp_mem`**: `A₀` stable under every smooth `ψ : ℝᵏ → ℝ` with `ψ 0 = 0` (BGL's diffusion-algebra
   hypothesis; unverified whether BGL restricts the class of ψ). The `diffusion` chain rule is now unconditional
   on `A₀` (guard "ψ(f) ∈ A₀" removed; `ψ 0 = 0` added). Consequence: the OU class "C^∞ with
   polynomial-growth derivatives" is not admissible (ERRATA G2); C_c^∞ or C^∞(𝕋) are.
R3. **Carré du champ** stays a pointwise field on `A₀`: `Γ f g x = (L (f*g) x − f x L g x − g x L f x)/2`.
   Only the product `f*g` (inside the non-unital algebra) is used; no unit. `L 1 = 0` is not visible on `A₀`:
   it is the case `k = 0`, `ψ ≡ 1` of `diffusion_A` (proved as `FullMarkovTriple.L_one`). `ibp` is symmetric in
   `(f,g)` on `A₀` (both slots equal by `Γ_symm`).
R4. **`FullMarkovTriple`**: `A : Subalgebra` (unital) with `A₀_le : ∀ f ∈ A₀, f ∈ A`, **`A_comp`** (stable under
   all smooth ψ), `diffusion_A` unconditional, Γ/L calculus on `A`, `esa` (unchanged range criterion),
   `ibp_A` (as before) and the NEW **`ibp_A_symm`** (`∫ f·Lg = −∫Γ(f,g)` for `f ∈ A`, `f,Lf ∈ L²`, `g ∈ A₀`).
   F6 choice: the field is the identity itself (it is a statement about the instance, provable by
   integration by parts for circle/ℝ/Gibbs), *not* the abstract conclusion "f ∈ D(L̄)": the conclusion is
   then DERIVED (`FullMarkovTriple.resolvent_eq`: R([f]−[Lf]) = [f] via ⟨R(u−v)−u,(1−L)g⟩ = 0 for `g ∈ A₀`
   and density of `(1−L)A₀`). I could not derive `ibp_A_symm` from `ibp_A` (it is the statement that `f` is in
   the maximal domain and not just a weak solution against `A₀`), hence a field. What the Bakry–Émery semigroup
   proof additionally needs (Γ(P_t f) ∈ L¹, ∫ L Γ(P_t f) = 0, i.e. integration against the constant 1 ∈ A \ A₀ in
   infinite measure) is NOT provided; for finite μ it follows from `resolvent_eq` with `f = Γ(P_t f)`
   (since `1 ∈ D(L̄)`, `L̄1 = 0`). Left to the Bakry–Émery development.
R5. **Markov property derived.** `Hilbert.isMarkovianForm : ∀ T : MarkovTriple E, IsMarkovianForm T`
   (the 'explicit hypothesis' of the bridge is removed). Proof: `ψ_δ(t) = √(t²+δ²) − δ` is smooth with
   `ψ_δ(0)=0`, so `ψ_δ(f) ∈ A₀` (`comp_mem`); chain rule gives `Γ(ψ_δ f) = ψ_δ'(f)² Γ(f) ≤ Γ(f)`; dominated
   convergence gives `ψ_δ(f) → |f|` in L² (`0 ≤ |f| − ψ_δ(f) ≤ min(δ,|f|)`); then the existing
   `isMarkovianForm_of_approx` (lower semicontinuity) concludes. Nothing remains open for positivity.
R6. **Conservativeness.** `IsSemigroupOf` is unchanged. For `FullMarkovTriple`, `P_t 1 = 1` is proved
   (`tripleSemigroup_one`), hence `Hilbert.isSemigroupOf_full` holds with no extra hypothesis. For a bare
   `MarkovTriple` it cannot hold in general (C_c^∞(0,1)); `isSemigroupOf_of_markov_conservative` takes it as a
   hypothesis. For infinite μ the clause is vacuous (ERRATA G1).
R7. **Unchanged**: `CD`/`CDFull`, `PoincareIneq`/`LogSobolevIneq` (with `IsProbabilityMeasure`), `ErgodicL2`/`ErgodicΓ`,
   `fisherInfo`/`IsFisherAdmissible`, `IsSemigroupOf`, `energy`, `Ent`, `Γ₂`, `semigroup_stable`.
R8. **Instances.** `trivialTriple`/`trivialFull` (A₀ = ⊤ non-unital); circle: `A₀ = {f | f∘(↑) : ℝ → ℝ is C^∞}`
   (trig polynomials are used only for density, `Atrig`); ℝ: `A₀ = C_c^∞(ℝ)`, density from
   `Lp.dense_hasCompactSupport_contDiff`, ibp from `integral_mul_deriv_eq_deriv_mul_of_integrable`.
   No `FullMarkovTriple` instance exists for circle or ℝ (needs `esa`, `semigroup_stable`).

## Design choices (Phase 2; items 2, 4, 6, 12 superseded, see above)

1. **`Γ`, `L : (E → ℝ) → (E → ℝ) → ...` total functions constrained only on `A₀`** (PLAN's first option). Alternative: functions out of `A₀` as a subtype (safer, clumsier). Worry: nothing pins `Γ f g` for `f ∉ A₀`; every statement must carry `f ∈ A₀` (CD, PI, LSI, energy do).
2. **`A₀ : Subalgebra ℝ (E → ℝ)`**: constants are in `A₀`, hence `1 ∈ Lᵖ`, hence **μ is finite** (BGL allows σ-finite, infinite). `sigmaFinite` is kept as a field though redundant. Alternative: `NonUnitalSubalgebra` (Lebesgue-type instances) and `1 ∈ A` only in the full triple. The task asked for constants in `A₀`.
3. **Integrability instead of boundedness**: `memLp` (all `p<∞`) + `measurable`, not "bounded", so polynomial algebras (OU) are admissible. BGL 3.1.1 also uses `∩ Lᵖ`. `p = 0` is included in `memLp` (harmless).
4. **Diffusion property conditional on `ψ(f) ∈ A₀`** (not stability of `A₀` under all smooth `ψ`). Weaker than BGL; consequence: a strange `A₀` might satisfy it vacuously for non-polynomial `ψ`. Auditor: look for a degenerate triple that exploits this (e.g. `A₀` tiny with Γ junk). Note `Γ(ψ f, g)` is only constrained for `g ∈ A₀`, and `ψ` ranges over `ContDiff ℝ ⊤`. Chain rule is for `k` variables via `Fin k → ℝ`, derivatives via `fderiv` (`pderiv`, `pderiv₂`); `L 1 = 0` is the case `k=0, ψ≡1` (not a field). Both chain rules (Γ and L) are fields although L's follows from Γ's plus `carre_du_champ` formally; redundancy kept for provers.
5. **Linearity of `Γ`** stated in the first variable + symmetry (`Γ_add`, `Γ_smul`); `L` linearity as `L_add`, `L_smul`. `Γ_nonneg` is pointwise (`∀ x`), as is `carre_du_champ` (DECISIONS 3).
6. **ibp** `∫ g * L f = -∫ Γ f g` as a field, on `A₀`. Integrability follows from `memLp` + `Γ_mem`/`L_mem` (Hölder), so Bochner junk is not an issue.
7. **Density**: `∀ p, Fact (1 ≤ p) → p ≠ ∞ → Dense {u : Lp ℝ p μ | ∃ f ∈ A₀, u =ᵐ f}`. The `Fact` binder is needed for the topology on `Lp`.
8. **`Γ₂`** pointwise as `(L Γ(f,f) − 2 Γ(f, Lf))/2`.
9. **`CD ρ n`, `n : ℝ≥0∞`**: `0 < n ∧ ∀ f ∈ A₀, ∀ᵐ x, ρ Γ f f x + (n⁻¹).toReal * (L f x)^2 ≤ Γ₂ f x`. `n=∞` gives coefficient 0 (`∞⁻¹=0`); finite `n>0` gives `1/n`; `n=0` is false by the conjunct (otherwise `(0⁻¹).toReal = 0` would silently equal `CD(ρ,∞)`). A.e. rather than pointwise (alternative: pointwise; the support issue). Sanity: `trivialTriple_CD`, `trivialTriple_not_CD_zero`. Open: BGL assumes `n ≥ 1`; here any `n>0` allowed.
10. **Energy** `∫ Γ f f dμ`; no domain/closure in the frozen surface. **Ent** `∫ f log f − (∫f) log(∫f)` with Mathlib's `log 0 = 0`; junk `0` when non-integrable; meant for `f ≥ 0`, probability `μ`. **Variance** is Mathlib's `ProbabilityTheory.variance` (no wrapper). **PI/LSI** include `IsProbabilityMeasure μ` as a conjunct (false otherwise) because Mathlib's variance and `Ent` are not normalised. LSI: `Ent(f²) ≤ 2 C ℰ(f)` (Gaussian has `C = 1`). **Fisher** `∫ Γ h h / h` (division by zero = 0).
11. **`IsSemigroupOf T P`** with `P : ℝ≥0 → L² →L L²`: id at 0, semigroup law, strong continuity at 0, self-adjoint, positivity preserving, `P t 1 = 1`, generator extends `L|A₀` (right limit of `t⁻¹(P_t u − u)`, stated for any `L²`-representatives `u,v`, avoiding `toLp` proofs). Unique iff `L|A₀` is ESA; otherwise several witnesses (e.g. Neumann vs Dirichlet). Not constructed; existence not asserted. Contractivity is not listed (follows). Alternative: characterise via resolvent or Mathlib `LinearPMap` generator.
12. **`FullMarkovTriple`**: extended algebra `A ⊇ A₀`, the whole Γ-calculus repeated on `A`, `esa`, `ibp_A`, `semigroup_stable`.
    * `esa` is the range criterion `(1 − L)A₀` dense in `L²` (valid because `L|A₀` is symmetric and `≤0` by ibp; Reed–Simon X.26). Chosen to avoid building a `LinearPMap` (well-definedness on a.e.-classes needs an argument). Auditor: check it is equivalent to ESA and that `(u =ᵐ f − L f)` is the right set.
    * `ibp_A`: `f ∈ A` with `f, Lf ∈ L²`; conclusion includes integrability of `Γ f g`. Not stated for all `f ∈ A` since that would be false for OU (growth).
    * `semigroup_stable`: quantifies over all `P` with `IsSemigroupOf`; vacuous if none exists, but `esa` makes the semigroup exist mathematically.
    * Not in BGL form: BGL's list (§3.4) is from memory; the author should compare. Missing: stability of `A` under smooth `ψ` (only conditional), `A ⊆ D_loc`-type conditions.

## Open worries (author)

* No nontrivial satisfiability evidence: the sanity instance has `L = Γ = 0` on a finite discrete space. The `Γ ≠ 0` case (OU on ℝ with polynomials, or circle) requires density of polynomials / trigonometric polynomials in Lᵖ and was not attempted. A genuine nonzero instance is the next sanity task; until then non-vacuity of `diffusion`, `dense` with `Γ≠0` is untested. Note finite spaces with `L ≠ 0` are impossible (diffusion property excludes jump generators).
* `A₀` closed under `Γ`, `L`, and `Γ ∈ A₀` forces e.g. for Gaussian `A₀` = polynomials: OK; for compactly supported smooth functions fine too.
* `MarkovTriple` has no field making `Γ`/`L` junk off `A₀` irrelevant; theorems about `Γ₂ f` for `f ∈ A₀` use `Γ₂ f` which evaluates `L (Γ f f)`: inside `A₀` by `Γ_mem`, good.
* μ finite is forced; the Lebesgue-measure/ℝⁿ-heat-semigroup case is excluded by design (PLAN's examples are all probability).

## Attack suggestions (auditor)

1. Exhibit a triple satisfying `MarkovTriple` for which a BGL consequence fails (e.g. non-uniqueness of `L` given `Γ`: ibp + dense gives `L f` a.e. only; pointwise `carre_du_champ` ties `L(fg)` but is `L` determined by `Γ`? check).
2. Pathological `A₀` where `diffusion` is vacuous beyond polynomials.
3. `IsSemigroupOf` satisfied by a non-Markov/non-minimal semigroup when `esa` fails; and whether `IsSemigroupOf` is satisfiable at all for nontrivial triples (e.g. `Lp` topology/`nhds 0` on `ℝ≥0` fine).
4. `CD` with a.e. vs `Γ₂` evaluated on junk off support; `n < 1` allowed.
5. `Ent`/Fisher junk values for non-integrable or negative `f`.

## Round 4 changes (ERRATA N4, N2, L1)

R7. **`MarkovTriple.memLp`** now quantifies over `1 ≤ p < ∞` only (was `p ≠ ∞`, which included
    `p ∈ [0,1)` and excluded e.g. classes decaying like `1/(1+x²)` for infinite μ). Instances
    (Trivial, Circle, Lebesgue) and users (`memLp2`, `integrable_of_mem`, Audit) updated.
R8. **`IsSemigroupOf`** gained the sub-Markov clause `∀ t (u : L²), u ≤ᵐ 1 → P t u ≤ᵐ 1`, stated on
    representatives (for infinite μ, `1 ∉ L²` but the hypothesis `u ≤ 1` a.e. is satisfiable); with
    positivity it is `0 ≤ u ≤ 1 ⇒ 0 ≤ P t u ≤ 1`. The clause `P t 1 = 1` is kept (meaningful for
    finite μ only). New separate predicate `IsConservative T P` (`P_t g ∈ L¹`, `∫P_t g = ∫g` for
    `g ∈ L¹ ∩ L²`), NOT part of `IsSemigroupOf`. Docstring uniqueness claim softened (L1).
    Audit points: (i) the clause is implied by the other clauses for finite μ and conservativeness;
    (ii) it is proved for the Friedrichs semigroup of every `MarkovTriple`, so `isSemigroupOf_full`
    is still unconditional; (iii) `semigroup_stable` hypotheses are strengthened (extra clause on P)
    hence the field is weaker than before, which is harmless (still a field to be proved for the
    circle, where the Friedrichs semigroup satisfies the clause).
    Manifest hashes of Frozen/MarkovTriple.lean and Frozen/Semigroup.lean updated (status still
    `proposed`).

R9. **`FullMarkovTriple.ibp_AA`** (ERRATA P4-1) added: `∀ f ∈ A, ∀ k ∈ A, MemLp f 2 → MemLp (L f) 2 →
    MemLp k 2 → MemLp (L k) 2 → MemLp k ∞ → Integrable (Γ f k) ∧ ∫ k·L f = −∫ Γ f k`.
    Rationale: `ibp_A`/`ibp_A_symm` only pair against `g ∈ A₀`; semigroup interpolation needs `P_t h`
    and `Φ'(P_t h)` (both in `A ∖ A₀`) in both slots; derivation from `Γ g = ½L(g²) − gLg` is circular.
    Audit points: (i) is the L^∞ hypothesis on `k` the right/minimal one (BGL asks for `k` bounded
    with `k, Lk` in `L²`?); the `MemLp k 2` and `MemLp (L k) 2` hypotheses may be redundant;
    (ii) it implies `ibp_A` only for `g ∈ A₀` essentially bounded, which `memLp` already gives, so
    `ibp_A` could become a consequence (not simplified); (iii) true for circle and expected for OU
    on `C^∞` with polynomial growth only with extra growth control (OU instance: other agent);
    (iv) non-vacuity: circle (Γ ≠ 0) and trivial. BGL numbering unverified. Manifest updated
    (Frozen/FullMarkovTriple.lean); status still `proposed`.

---

# BGL comparison — checked against the book (Ch. 3, Defs 3.1.1–3.1.15, 3.3.1, 3.3.14, 3.3.25, summary §3.4)

Labels D1–D9, S10–S11, F1–F10 are the book's own labels in its §3.4. Statements below are paraphrases.
Status: **MATCH** (same content), **STRONGER** (ours implies the book's), **EQUIV** (equivalent under stated conditions),
**MISSING** (the book requires it, our surface does not), **EXTRA** (ours, not in the book).

## Diffusion Markov Triple (D1–D9)

| Book | Our surface | Status |
|---|---|---|
| D1 σ-finite μ (probability if finite) | σ-finite μ; finite μ allowed with any mass (PI/LSI add `IsProbabilityMeasure`) | MATCH (slightly more general) |
| D2 A₀ an algebra of **bounded** functions, dense in all Lᵖ (1≤p<∞), stable under smooth ψ with ψ(0)=0 | non-unital algebra, `memLp` for 1≤p<∞, `dense`, `comp_mem` | MATCH up to null sets (ours gives essential boundedness, audit N1; the book's boundedness is everywhere) |
| Def 3.1.1: increasing sequence in A₀ converging a.e. to 1 | not present | **MISSING** (it gives the meaning of "1" when μ is infinite) |
| D3 Γ symmetric bilinear A₀×A₀→A₀, Γ(f,f)≥0, diffusion property, with the fundamental identity | same, via the pointwise carré-du-champ identity and k-ary chain rule | STRONGER (pointwise identity; the book's identity is a.e.) |
| D4 continuity of g↦∫Γ(f,g) in L² | follows from L(A₀)⊂A₀⊂L² and ibp | derivable |
| D5 L defined by integration by parts; chain rule for L follows | L is a field, ibp is a field, chain rule for L is also a field | EXTRA redundancy, consistent |
| D6 L(A₀)⊂A₀ | `L_mem` | MATCH |
| D7 D(E), D(L) by completion / Friedrichs | Hilbert layer (`FormData`, Friedrichs) | MATCH |
| D8 ∫Lf dμ = 0 for f∈A₀ | **not a field of `MarkovTriple`**; derived only for `FullMarkovTriple` (via `ibp_A_symm` with f=1) | **MISSING** from the bare structure |
| D9 P_t from the self-adjoint L; positivity preserving and sub-Markov | `IsSemigroupOf` characterizes P_t by 8 clauses incl. positivity, sub-Markov, generator extends L; existence proved (`isSemigroupOf_full`) | EQUIV in spirit (characterization instead of construction) |

## Standard triple (S10–S11)

| Book | Our surface | Status |
|---|---|---|
| S10 ergodic: f∈D(L), Lf=0 ⇒ constant (equivalently f∈D(E), Γ(f)=0 ⇒ const) | `ErgodicL2` is on the closure of L|A₀ (kernel is constants); `ErgodicΓ` on A₀ only | EQUIV under ESA; `ErgodicΓ` is weaker than the book's second form |
| S11 conservative: P_t(1)=1, P_t acting on bounded measurable functions, also for infinite μ | clause `P t 1 = 1` in `IsSemigroupOf` (vacuous for infinite μ); `IsConservative` is a separate predicate | **DIFFERENT** — the book notes ESA alone doesn't give conservativeness but ESA+CD(ρ,∞) does (Thm 3.3.23); ours has no such theorem |

## Full triple (F1–F10)

| Book | Our surface | Status |
|---|---|---|
| F1 ideal property: f∈A, h∈A₀ ⇒ hf∈A₀ | not present | **MISSING** |
| F2 positivity detection: f∈A with ∫hf≥0 ∀ positive h∈A₀ ⇒ f≥0 | not present | **MISSING** |
| F3 A stable under all smooth ψ | `A_comp` | MATCH |
| F4 L: A→A extends L; Γ on A is given by the carré-du-champ formula | `diffusion_A`, fields for L,Γ on A (pointwise identity) | MATCH/STRONGER |
| F5 Γ(f)≥0 on A | `Γ_nonneg_A` | MATCH |
| F6 change-of-variables formulas on A | `diffusion_A` | MATCH |
| F7 ∫Γ(f,g) = −∫gLf = −∫fLg for **all** f∈A, g∈A₀ | `ibp_A`, `ibp_A_symm` stated only for f, Lf ∈ L² | **DIFFERENT** (weaker hypotheses on the conclusion; the book gets integrability from F1, which we lack) |
| F8 P_t f ∈ A for f∈A₀ | `semigroup_stable` (for every P with `IsSemigroupOf`) | EQUIV |
| F9 connexity: f∈A, Γ(f)=0 ⇒ constant | not present (we use `ErgodicL2`) | **MISSING** |
| F10 ESA | `esa`: Ran(1−L|A₀) dense in L² | EQUIV (standard criterion for a symmetric operator) |
| — | `ibp_AA` (mixed integration by parts on A with bounded test function) | **EXTRA** — not in the book |
| CD(ρ,n) defined on all of A (Def 3.3.14), n∈[1,∞] | `CD` on A₀, `CDFull` on A; n>0 allowed (not only n≥1) | DIFFERENT (split; wider n range) |

## How the book proves its theorems (relevant to our extras)

The book does **not** use anything like `ibp_AA`. Under ESA + CD(ρ,∞) it extends Γ₂ and the CD inequality from A₀ to D(L)
(Prop 3.3.16), identifies Γ₂ on A∩D(L) with the one on D(L) and gets ∫Γ₂(f)=∫(Lf)² there (Prop 3.3.17), then proves the
strong gradient bound by a spectral argument (Thm 3.3.18, Lemmas 3.3.20–3.3.21), and mass conservation as a *consequence*
of ESA + CD(ρ,∞) (Thm 3.3.23). Our LSI proof instead uses `ibp_AA` and the hypothesis `BEStable`.

## Conclusions

1. The surface is **not** a faithful transcription of the book. It proves the same classical constants and agrees with the
   book on the diffusion/standard layer (D1–D9 modulo D8 and the exhaustion sequence), but its Full layer differs.
2. Missing BGL requirements: exhaustion sequence (Def 3.1.1), D8, F1 (ideal), F2, F9, and the Thm 3.3.23 route to conservativeness.
3. Extra non-BGL ingredients: `ibp_AA`, the split `CD`/`CDFull`, the L²-restricted `ibp_A`, `ibp_A_symm`, `IsSemigroupOf` as a characterization, and `BEStable`.
4. Our instances (circle, Lebesgue, OU) do satisfy the book's F1–F10 in spirit (smooth C_c^∞ / C^∞ classes, ideal property holds),
   so realigning is plausible, but it has NOT been checked in Lean.
