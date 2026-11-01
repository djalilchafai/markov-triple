# FROZEN_REVIEW: Phase 2 frozen definition surface (status: all `proposed`)

Files: `MarkovTriple/Frozen/{PartialDeriv,MarkovTriple,Gamma2,CD,Energy,Ent,Poincare,LSI,Fisher,Semigroup,FullMarkovTriple}.lean`.
Sanity (not frozen): `MarkovTriple/Sanity/Trivial.lean`. Manifest: `frozen-manifest.json`; check with `scripts/check_frozen.py`.
BGL numbering in docstrings is partly from memory; entries marked "numbering to be verified" must be checked against the book.
`Frozen/Basic.lean` is the old placeholder, not in the manifest.

## Design choices

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
