# AUDIT_PHASE4 (round 4, hostile) — FunctionalInequalities + Hilbert/SubMarkov

Scope: `FunctionalInequalities/{GapFromSquare,TripleSquare,Poincare}.lean`, `Frozen/{CD,CDFull,Poincare,Ergodic,FullMarkovTriple,MarkovTriple,Semigroup,Gamma2,Energy}.lean`,
`Hilbert/SubMarkov.lean`, `FullBridge.lean` (`resolvent_eq`, `L_one`). FI_STATUS.md read only after forming the view.
Frozen manifest hashes: all 13 files match `frozen-manifest.json`. No `sorry` in scope.
New files (none imported by the root): `Audit/Phase4Axioms.lean`, `Audit/Phase4NonVacuous.lean`, `Audit/Phase4Curvature.lean`.

## Verdicts

| # | question | verdict |
|---|----------|---------|
| 1 | `poincare_of_CD_infty` non-vacuous? | YES (machine-checked, degenerate witness) + non-degenerate candidate checked on paper/partly in Lean. No HIGH. |
| 2 | proof steps / hidden junk | No junk found. Every step checked (details below). |
| 3 | finite-n constant | Correct: `(1-1/n)/ρ = (n-1)/(ρ n)` = 1/(Lichnerowicz gap ρn/(n-1)); n ≤ 1 excluded by `1 < n`. Sharp on S² (checked, below). |
| 4 | SubMarkov / `IsSemigroupOf` | Statement non-trivial, proof correct, clause order does not change meaning. |
| 5 | axioms | 36 constants in the 4 modules (all non-internal decls, aux lemmas included): only propext/Classical.choice/Quot.sound. |

## (1) Non-vacuity

`Audit/Phase4NonVacuous.lean` (compiles, axioms standard): on the one-point probability space with `Sanity.trivialFull`
(`Γ = L = 0`): `FullMarkovTriple` + `IsProbabilityMeasure` + `CD 1 ∞` + `ErgodicL2` all hold, and `poincare_of_CD_infty onePt one_pos ..`
typechecks. So the hypotheses are jointly satisfiable. **Caveat (MEDIUM, M-1):** this witness has `Γ = 0`, so it exercises none of the
analytic content; no instance with `Γ ≠ 0`, `ρ > 0` is in the library (circle has ρ = 0).

Non-degenerate candidate = OU on `(ℝ, γ)`, `A₀ = C_c^∞(ℝ)`, `A = C^∞(ℝ)`, `L f = f'' - x f'`, `Γ = f'g'`. Field-by-field (mathematical check):
* N1 (`comp_mem` for all smooth ψ + `memLp` ⇒ A₀ essentially bounded; true: choose ψ growing fast along levels `a_k` with `μ(|f|>a_k)>0`) is respected: C_c^∞ is bounded; polynomials are excluded (already `Audit/Frozen3OU`).
* `comp_mem` (ψ(0)=0 keeps compact support), `Γ_mem`, `L_mem`, `dense`, `memLp`, `ibp` (weight `e^{-x²/2}`, compact support), `diffusion`: classical.
* `A = C^∞(ℝ)` is closed under all smooth ψ, `L`, `Γ`; `Γ_nonneg_A`, `carre_du_champ_A`, pointwise on all of ℝ: fine. `ibp_A`, `ibp_A_symm`: only local (test function compactly supported) — true, no boundary term at ∞.
* `esa`: `(1-L)C_c^∞` dense in `L²(γ)` (cutoff gives polynomials ⊂ closure; `(1-L)` is triangular on polynomials with leading coeff `1+d`; polynomials dense). True.
* `semigroup_stable`: any `P` with `IsSemigroupOf` has self-adjoint generator extending the e.s.a. `L|A₀`, so `P = e^{tL̄}` = Mehler; `P_t u ∈ C^∞` for `t>0`. True.
* `ErgodicL2`: true (spectral gap 1). `CD(1,∞)` on every smooth f: **machine-checked pointwise** (`Audit/Phase4Curvature.lean`, `ou_Gamma2`: `Γ₂ f = f''² + f'²`, `ou_CD_infty`).
* Output consistency: theorem yields `PI(1)` = Gaussian Poincaré, sharp. No contradiction.
Remaining Lean work for OU: `esa`, `semigroup_stable` (uniqueness + Mehler smoothing), `ErgodicL2`, `diffusion` for k-ary ψ. Estimated several hundred lines each; none is a theoretical obstruction.

Second candidate, Legendre/zonal `S²` on `[-1,1]` (`L = ((1-x²)f')'`): `lg_Gamma2`, `lg_CD_two` machine-checked (`Γ₂ = Γ + ((1-x²)f''-xf')² + x²f'²`, hence `CD(1,2)`, i.e. Lichnerowicz gap `ρn/(n-1) = 2 = λ₁(S²)`, sharp). Instance pitfalls (INFO I-1..I-3):
* I-1: `A` must be `C^∞` up to the boundary. For `A = C^∞(-1,1)`, `f = log(1-x)` has `f, Lf ∈ L²` and `∫ g Lf ≠ -∫Γ(f,g)` (difference `2g(1)`): endpoints are limit-circle; `L` is e.s.a. on polynomials but NOT on `C_c^∞(-1,1)`.
* I-2: `esa` is easy here (Legendre/triangular on polynomials) but `semigroup_stable` needs `C^∞`-regularity of `P_t u` up to the boundary (derivative bounds on Legendre polynomials) — harder than OU.
* I-3: fields `Γ_nonneg(_A)`, `carre_du_champ(_A)`, `diffusion(_A)` are pointwise for ALL `x : E`, so the cheap "E = ℝ, μ on [-1,1]" model fails (`Γ = (1-x²)f'²<0` for |x|>1); `E` must be the subtype `Icc (-1) 1` with `derivWithin`.

## (2) Proof audit (poincare_of_CD_infty / rho_var_le_of / square_all)

* `∫ L h = 0`: `ibp_A_symm` with `f = 1`; needs `1 ∈ A` (`A.one_mem`), `MemLp 1 2` (finite μ), `MemLp (L 1) 2`, `L 1 = 0` (`diffusion_A`, k = 0, ψ ≡ 1; sum over `Fin 0` empty), `Γ(1,h) = 0` (same). OK. (Real instances satisfy k=0 case iff `L1=0`; the non-conservative Dirichlet triples are correctly excluded from `FullMarkovTriple`.)
* `∫Γ₂ g = ∫(Lg)²`: `Γ g g, L g ∈ A₀`, integrability from `memLp`, `ibp` for `∫ g' Lg`. Pointwise `Γ₂` is only used inside `integral_mono_ae` with the a.e. `CD`: a.e. vs pointwise handled correctly.
* `square_all`: set of `w` with the squared inequality is closed (continuity of `R`, inner, norm), contains `(1-L)A₀` (via `R(g-Lg) = g`, `inner_Lt0_toLp0`), `esa` gives density. For `y = g - Lg`: `y - Ry = -Lg`, `⟪-Lg,g⟫ = ∫Γ(g,g)`; the inequality reads `ρ∫Γ ≤ ‖Lg‖²`. OK.
* `esa` statement = range criterion (Reed–Simon X.26, `L ≤ 0` symmetric); used only via `closure_eq`. `resolvent_eq` (FullBridge): `⟪R(u-v)-u,(1-L)g⟫ = 0` by both ibp fields; `L` symmetric slot is the one that matters. OK.
* Centering: `g - m = g + (-m)•1 ∈ A` (A unital subalgebra), `L(g-m) = Lg` (`L_add_A`, `L_smul_A`, `L_one`). `MemLp` OK. `horth`: fixed vectors are a.e. constants (`fixed_const` through `generator_graph_eq_closure` + `ErgodicL2`, sequence form matches `ErgodicL2` exactly), `⟨w,c⟩ = c(∫g - m) - c∫Lg = 0`. OK.
* Final algebra: `‖u‖² = ∫(g-m)² = variance` (`variance_eq_integral` needs only AEMeasurable; `g ∈ L²`, probability: no junk), `⟪Lg, g-m⟫ = ∫ gLg = -∫Γ(g,g)` using `∫Lg = 0` and `ibp`. `ρ` unrestricted in `rho_var_le_of` (ρ ≤ 0 trivial); `hρ : 0 < ρ` only used for division. `Ent`/`variance` junk: none, because `f ∈ A₀ ⊂ L²`.
* `ErgodicL2` uses `eLpNorm → 0` in `ℝ≥0∞`: non-L² junk impossible (would be `∞`).
* Not used by the theorem: `semigroup_stable`, `ibp_A`, `Γ_nonneg_A`, ... (the Poincaré proof needs only a sub-structure; the instance burden is nevertheless the full structure).

Remaining honest gaps (not bugs): conclusion is on `A₀` only; `CD` only on `A₀` (that is all the integrated route needs).

## (3) Finite n
`CD ρ n`: `ρ∫Γ + (1/n)∫(Lg)² ≤ ∫(Lg)²` ⇒ `(ρ n/(n-1))∫Γ ≤ ∫(Lg)²` ⇒ `PI((n-1)/(ρ n))`. `hc : n⁻¹.toReal < 1` from `1 < n`; n = ∞ gives `c = 0`. Sharpness: zonal S² (ρ=1,n=2): `PI(1/2)`, `λ₁(S²)=2` (`lg_CD_two` machine-checked). n = 1 (c = 1) gives `ρ∫Γ ≤ 0`, no content, correctly excluded; `0 < n < 1` is admitted by the frozen `CD` (L-1: harmless, forces Γ=0-type degeneracy) but excluded in the theorem.

## (4) SubMarkov
* Clause: `u ≤ᵐ 1 → P t u ≤ᵐ 1` for `u : L²`; non-trivial for infinite μ (u can be ≪ 0 on large sets; not implied by `P t 1 = 1`, which is vacuous there); with positivity + linearity gives `|u| ≤ 1 ⇒ |P u| ≤ 1` (satisfied by neither `P = 0` + `P 0 = id`, nor by general contractions). Docstring order (positivity, sub-Markov, `P 1 = 1`, generator) = definition order = proof order; the manifest matches; all consumers typecheck positionally, so no meaning change.
* `resolvent_pairing_nonpos`: `⟪g-λu, φ-u⟫ = E(u,φ)-E(u) ≤ (E(φ)+E(u))/2 - E(u) ≤ 0`. Correct.
* `resolvent_le_one`: `c = 1/λ`, `w = u∧c - u ≤ 0`; on `{u>c}`, `(g-λu)w ≥ (λu-1)(u-c) = λ(u-c)²` because `g ≤ 1`; so `λ∫w² ≤ ⟪a,w⟫ ≤ 0` ⇒ `w=0` ⇒ `λu ≤ 1`. Correct.
* `isClipForm`: `ψ_δ(0)=0`, `|ψ_δ'|≤1`, `ψ_δ→t∧c` uniformly (`clipFn_bounds`), `Γ(ψ(f)) = ψ'(f)²Γ(f) ≤ Γ(f)` via `diffusion`; `Tm` Lipschitz-1 ⇒ extends to `Q` by `exists_contraction_of_approx`. Correct; `memLp_clip` needs `c ≥ 0` (given).
* Invariance of `{w ≤ 1}`: closed (a.e. subsequence), stable under all `λR_λ`; `semigroup_mapsTo` needs only closed + invariance (Euler/Yosida limit), no convexity. Correct.

## (5) Axioms
`Audit/Phase4Axioms.lean`: walk of all non-internal constants whose defining module is one of the 4 modules (36 constants, ~2 min): 0 with non-standard axioms. `Phase4NonVacuous`, `Phase4Curvature` theorems: standard axioms only. Full-project walk not run.

## Findings list
* M-1 (MEDIUM, `FI_STATUS`/library): no `Γ ≠ 0, ρ > 0` instance; `poincare_of_CD_infty` only exercised on the 1-point triple. Fix: OU instance (recommended, see above).
* M-2 (MEDIUM, for LSI): fields missing for the semigroup interpolation, see next step.
* L-1 (LOW, `Frozen/CD.lean:20`): `CD ρ n` admits `0<n<1`. Harmless.
* I-1..I-3 (INFO): Legendre instance pitfalls above.
* No HIGH finding, no counterexample to any proved statement.

## Next step: what LSI needs (prioritized)
1. **Diagonal / mixed IBP on `A`** (the real blocker; not derivable from current fields): for `f,k ∈ A` with `f,Lf,k,Lk ∈ L²` (bounded `k`), `Γ(f,k) ∈ L¹` and `∫ k Lf = -∫Γ(f,k)`. Reason: `ibp_A` only tests against `A₀`, and `P_t h ∈ A∖A₀`, `Φ'(P_t h) ∈ A∖A₀`. Attempted derivation is circular: `Γ g = ½L(g²) - gLg` needs `L(g²)∈L¹`, i.e. `Γ g ∈ L¹`; there is no continuity field tying pointwise `Γ` on `A` to the closed form. Add a field (e.g. `ibp_AA`) or a closability field. (The weaker `∫ L k = 0` for `k ∈ A, k,Lk ∈ L²` IS derivable now: `1 ∈ D(L̄)`, `L̄1 = 0` via `resolvent_eq`, self-adjointness of the generator.)
2. Use `CDFull` (CD on `A`) as hypothesis: `P_t h ∈ A` is not in `A₀`. `CDFull.toCD` already gives the converse direction.
3. L^∞ bounds for `P_t h`: `ε ≤ h` ⇒ `ε ≤ P_t h ≤ ‖h‖_∞` from positivity + new sub-Markov clause + `P_t 1 = 1` (finite μ). All available now (this is where N2 pays off).
4. L²→L¹ chain rule for `t ↦ ∫Φ(P_t h)`, `Φ(x)=x log x` modified to a smooth function outside `[ε, M]` so `ψ(f) ∈ A` (`A_comp`); derivative `⟨Φ'(P_t h), L̄P_t h⟩` using `semigroup_stable` + `resolvent_eq` (gives `P_t h ∈ D(L̄)` with `L̄ = L` pointwise). Time derivative of `Γ(P_t h)`-type integrals (`Fisher` decay `I' ≤ -2ρ I`) needs item 1 again plus Γ₂-calculus on `A` (`diffusion_A` OK).
5. Convergence `Ent(P_t h) → 0`: `PI(1/ρ)` on `A₀` ⇒ `HasSpectralGap` of the Friedrichs generator needs extension of PI from `A₀` to the form domain (FI_STATUS "Not done"; routine by closure of the form, but unwritten) then `hasExpDecay_of_hasSpectralGap`.
6. Ent junk: for `f ∈ A₀`, `f² log f²` is integrable from `memLp 3` (`x²|log x²| ≤ C(1+|x|³)`); state `LogSobolevIneq` consumers with an explicit integrability lemma to avoid Bochner junk.
7. Provide at least one `Γ ≠ 0, ρ>0` instance (M-1) before LSI, otherwise LSI is again only tested on the 1-point triple.
