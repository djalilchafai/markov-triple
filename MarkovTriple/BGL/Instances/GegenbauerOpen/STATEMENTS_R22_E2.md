# STATEMENTS R22-E2 -- zonal Gegenbauer on (-1,1) with C_c^infty((-1,1)): towards a NON-COMPLETE FullTriple

Method "Armstrong": statements first (written before any proof); deviations are logged in the final Status section.
Namespace `MarkovTriple.BGL.Instances.GegenbauerOpen`, directory `MarkovTriple/BGL/Instances/GegenbauerOpen/`.

## Choice of parameter: lambda = 3/2 (n = 2 lambda + 1 = 4, zonal part of S^4 minus its two poles)

Justification: lambda >= 3/2 is the range where F10 can hold (ERRATA R21-4).  For lambda = 3/2 the weight is
`w(x) = 1 - x^2`, the operator is `L f = (1-x^2) f'' - 4 x f'`, and `w * (1-x^2) = (1-x^2)^2` is a
polynomial: `w L f = ((1-x^2)^2 f')'`.  Everything is polynomial in `x`, so no `rpow` calculus is needed;
general lambda would add `Real.rpow` derivatives at every step for no new phenomenon.
The reference probability measure is the normalised weight: `mu = (3/4) (1-x^2) dx` on `(-1,1)`
(`int_{-1}^1 (1-x^2) dx = 4/3`), since `DiffusionTriple.finite_prob` requires a probability measure.

## Data

```lean
/-- (3/4)(1-x^2) dx on (-1,1), a probability measure on R. -/
noncomputable abbrev goμ : Measure ℝ :=
  (volume.restrict (Set.Ioo (-1:ℝ) 1)).withDensity (fun x => ENNReal.ofReal (3/4 * (1 - x^2)))
/-- C_c^infty((-1,1)) : smooth f with tsupport f ⊆ Ioo (-1) 1. -/
def goA₀ : NonUnitalSubalgebra ℝ (ℝ → ℝ)
noncomputable def goL (f : ℝ → ℝ) : ℝ → ℝ := fun x => (1 - x^2) * deriv (deriv f) x - 4 * x * deriv f x
noncomputable def goΓ (f g : ℝ → ℝ) : ℝ → ℝ := fun x => (1 - x^2) * (deriv f x * deriv g x)
noncomputable def goDiff : DiffusionTriple ℝ     -- μ := goμ, A₀ := goA₀, Γ := goΓ, L := goL
```

## Statements

* **S1** `goDiff : DiffusionTriple ℝ`, all fields proved: finite_prob (`IsProbabilityMeasure goμ`), D2 density of
  `goA₀` in `Lp ℝ p goμ` (`1 ≤ p < ∞`; `theorem goA₀_dense`), exhaustion `u_n(x) = ivcut n ((x+1)/2)`,
  weighted IBP `∫ g (L f) dμ = -∫ Γ(f,g) dμ`, chain rule, `∫ L f dμ = 0`.
* **S2a** `theorem go_not_complete : ¬ goDiff.IsComplete` (key lemma `go_le_of_Γ`:
  `Γ ζ ζ ≤ c²` and `ζ ∈ goA₀` imply `ζ x ≤ c π` for all `x`).
* **S2b** (Γ₂, curvature).  `goDiff.ΓA f g x = (1-x²) f'(x) g'(x)` for smooth f, g, and for smooth f
  `goDiff.Γ₂ f f x = ((1-x²) f'' - x f')² + 3 x² f'² + 3 (1-x²) f'²` (the Bochner form `|Hess f|² + Ric(∇f)` on zonal
  functions of S⁴, `Ric = 3`; theorem `go_Γ₂_eq`), and `GoCD ρ n` (same body as `FullTriple.CD`, pointwise on all
  smooth f, as `IvCD` in R21): `theorem goDiff_CD : GoCD 3 4` (CD(n-1, n), n = 4: `3 Γ f + (1/4)(L f)² ≤ Γ₂ f`), and
  `GoCD ρ n` for every `ρ ≤ 3`, `4 ≤ n ≤ ∞` (as first drafted this said `1 ≤ n ≤ 4`, a mis-statement: CD(ρ,n) gets
  WEAKER as n grows, so `n ≥ 4`; corrected before proof, see Status; `GoCD` is pointwise on `x ∈ (-1,1)` only, since `Γ ≥ 0` needs `|x| ≤ 1`).
* **S3** (F1-F10 over `goA₀`): NOT attempted as Lean proofs; see Status for the exact open lemmas (F10 route and F8).

## DIFFERENCE FROM BGL

1. lambda = 3/2 only (BGL has general zonal Gegenbauer on `[-1,1]` with 𝒜₀ the polynomials).  The test algebra is
   `C_c^∞((-1,1))`, deliberately NOT BGL's.
2. `CD` is stated as `GoCD` (body of `FullTriple.CD`, pointwise on smooth functions) since no `FullTriple` is built.
3. Functions are `ℝ → ℝ` vanishing off `(-1,1)`; `mu` is the weighted measure on `ℝ` supported in `[-1,1]`.

## Status

Furthest stage: **S1 and S2 (both parts) PROVED; S3 NOT reached (no F-field beyond F-data of `DiffusionTriple` proved)**.
Build of `MarkovTriple.BGL.Instances.GegenbauerOpen.{Basic,Diffusion,NotComplete,Curvature,AxiomCheckR22E2}`:
0 errors, 0 warnings, no `sorry`, no `set_option`, axioms only `propext`, `Classical.choice`, `Quot.sound`
(`AxiomCheckR22E2.lean`).  No frozen file, `lakefile.toml`, `lake-manifest.json`, toolchain, `ERRATA.md`, `GAPS.md`,
`MarkovTriple.lean` touched.

Theorems (all in namespace `MarkovTriple.BGL.Instances.GegenbauerOpen`):
* `Basic.lean`: `goμ`, `isProb_goμ` (probability measure, `(3/4)(1-x²)dx`), `goμ_le`, `integral_goμ`, `goA₀`, `gocut` (+ `gocut_mem`,
  `gocut_mono`, `gocut_tendsto`), **`goA₀_dense`** (`C_c^∞((-1,1))` dense in `Lᵖ(goμ)`, `1 ≤ p < ∞`).
* `Diffusion.lean`: `goL`, `goΓ`, `deriv_goP` (`((1-x²)² f')' = (1-x²) L f`), `integral_go_L` (weighted IBP),
  `integral_go_L_self` (D8), **`goDiff : DiffusionTriple ℝ`** (S1, every field proved).
* `NotComplete.lean`: `goΓ_le_of_ae`, `go_le_of_Γ` (`Γζ ≤ c²` ⇒ `ζ ≤ cπ`, via monotonicity of `c·arcsin - ζ`),
  **`go_not_complete : ¬ goDiff.IsComplete`** (S2a).
* `Curvature.lean`: `go_ΓA` (`ΓA f g = (1-x²) f'g'`), **`go_Γ₂_eq`** (`Γ₂ f f = (1-x²)²f''² - 2x(1-x²)f'f'' + (3+x²)f'²` for all
  smooth `f`, equal to the Bochner form `((1-x²)f''-xf')² + 3x²f'² + 3(1-x²)f'²`), `GoCD`, **`goDiff_CD : GoCD ρ n` for
  `ρ ≤ 3`, `4 ≤ n`** (S2b; in particular `CD(3,4) = CD(n-1,n)` for `n = 4`).

Deviations from the statements as first written (nothing weakened while proving):
1. `GoCD ρ n` first drafted as "`ρ ≤ 3`, `1 ≤ n ≤ 4`": wrong direction (the `(1/n)(Lf)²` term only gets easier for larger `n`);
   corrected BEFORE proving to `4 ≤ n`.  CD(3,n) for `n < 4` is not claimed (expected to fail since `n = 4 = dim S⁴` is the sharp dimension; not checked in Lean).
2. `GoCD` is pointwise on `x ∈ (-1,1)` (not all of `ℝ`, unlike `IvCD`): `ρ Γ ≤ 3 Γ` needs `Γ = (1-x²)f'² ≥ 0`.  `CD(3,4)` itself holds on all of `ℝ`
   (the proof uses only `Γ₂ - 3Γ - L²/4 = (3/4)(a-b)² ≥ 0`), but the library CD is a.e. so only `(-1,1)` matters.
3. `Γ₂` closed form in the statement block: the first draft already had the Bochner form; proved verbatim.

### Why `λ = 3/2` and not general `λ`
Only for the polynomial weight is the calculus elementary (`w(1-x²) = (1-x²)²`).  General `λ ≥ 3/2` needs `rpow` derivatives
and an `rpow` normalisation constant; no new phenomenon (non-completeness is `λ`-independent: `∫ dx/√(1-x²) = π`).

### S3 (the `FullTriple` fields F1-F10): NOT DONE -- exact open lemmas
Candidate extended algebra `𝒜 = {f : ℝ → ℝ | Measurable f ∧ ContDiffOn ℝ ⊤ f (Ioo (-1) 1)}` (smooth in the open interval, NO behaviour
at the endpoints; unital).  Status of each field:
* F1 (ideal), F3, F4 (`L 𝒜 ⊆ 𝒜`), F5, F6, F7 (IBP for `f ∈ 𝒜`, `g ∈ 𝒜₀`), F9 (connexity: `Γ f = 0` a.e. ⇒ `f' = 0` on `(-1,1)` ⇒ constant):
  elementary, same calculus as S1 (est. 400-600 lines); F2 (positivity detection): bump-function argument, est. 100 lines.  NOT written.
* S10 ergodic and S11 conservative (needed by `StandardTriple`): S11 would follow from F10 by `DiffusionTriple.conservative_of_esa`
  (`Theory/ESAOne.lean`, finite measure); S10 needs F10 plus a weak-derivative argument.  NOT written.
* **F8 (`semigroup_A`: `P_t f ∈ 𝒜` for `f ∈ C_c^∞`)**: this is smoothness of `P_t f` in the OPEN interval (interior regularity for the
  Friedrichs semigroup).  The Sphere `FullTriple` gets F8 for free from the polynomial algebra (finite spectral sums); here `f` is not a
  finite sum of Gegenbauer polynomials.  Needs either (i) the Gegenbauer eigenbasis with `C^∞_loc` convergence of `Σ e^{-t k(k+3)} c_k G_k`
  (derivative bounds `‖G_k^{(j)}‖ ≤ poly(k)`, rapid decay of `c_k`), or (ii) 1-D elliptic regularity (`u ∈ 𝒟(G^∞)` ⇒ `u ∈ C^∞(-1,1)`
  from the ODE `((1-x²)² u')' = (1-x²)(…)`).  Est. 800+ lines.  This is the riskiest field, not attempted.
* **F10 (`ESAProp goDiff`), the crux**: TRUE by hand (Weyl): `Lf = 0` has solutions `1` and `∼ (1-x)^{-1}` at `x → 1` (since
  `f' = C/(1-x²)²`); `|f|² (1-x²) ∼ (1-x)^{-1}` is not integrable, so both endpoints are limit-point (`n = 4 ≥ 4`, consistent with ERRATA R21-4) and
  `L|C_c^∞(-1,1)` is essentially self-adjoint.  A Lean proof has not been attempted.  Candidate routes, in order of feasibility:
  (A) capacity route with the polynomial `FullTriple` of `Instances/Sphere`: show that the `Lcls`-graph closure of `C_c^∞(-1,1)` contains the
  polynomials.  Need cut-offs `ζ_k ∈ C_c^∞(-1,1)`, `ζ_k → 1` with `‖Γ(ζ_k)‖_{L^1(μ)}`-type bounds AND `‖(Lζ_k) p‖_{L²(μ)} → 0` for polynomials `p`:
  `L ζ_k = (1-x²)ζ_k'' - 4xζ_k'`, `∫ (Lζ_k)² dμ = (3/4)∫ ((1-x²)... )`; with log-type cut-offs `ζ_k` near `±1` this tends to `0` because the
  endpoints have zero capacity for `n ≥ 4` (`∫ (1-x)^{-?}` diverges for the Hardy weight).  This needs the explicit cut-off estimates
  (est. 300 lines) plus the identification of the Friedrichs domain with the closure of the polynomial algebra (the Sphere triple's own F10
  gives that polynomials are a core for the SPHERE generator, whose underlying measure is the same `goμ` on the zonal part; but the Sphere
  triple lives on `S⁴`, not on `(-1,1)`, so a zonal reduction (transfer of `generator`) is a further ~500 lines).
  (B) direct Weyl limit-point criterion in `L²`, from scratch (no Mathlib support): larger.
* Corollary if S3 were done: a non-complete `FullTriple` with `CD(3,4)` (`go_not_complete`, `goDiff_CD`).

### Remaining converse hypotheses (`FullTriple.mem_domain_of_Γ₂_direct`, ERRATA R20-M1)
That theorem needs: a `FullTriple` (F1-F10, S10, S11) AND `IsComplete` AND the CD/Γ₂ hypothesis.  For `goDiff` we have proved: the
`DiffusionTriple` axioms (S1), `¬ IsComplete` (S2a: it is outside the hypotheses of that theorem even if S3 held), curvature `CD(3,4)` in
`GoCD` form (S2b).  Still missing for any application of the converse: the `FullTriple` structure itself (F8, F10, F1-F7, F9, S10, S11 above) and
completeness, which is FALSE here.  So `goDiff` would be a non-complete `FullTriple` with CD, i.e. a test that completeness is
a genuine hypothesis of the direct converse (to be settled by a separate argument: for `goDiff` the conclusion of the converse would have to be tested
on `f ∈ 𝒜` with `Γ₂(f) ≥ 0`-type bounds but `f ∉ 𝒟(L)`, e.g. `f` blowing up like `(1-x)^{-1/2+ε}`... not attempted).

### Proposed ERRATA rows (ERRATA.md/GAPS.md NOT edited)
| id | severity | finding | resolution |
|---|---|---|---|
| R22-E2-1 | INFO | `goDiff : DiffusionTriple ℝ` (zonal Gegenbauer `λ = 3/2` on `(-1,1)`, `𝒜₀ = C_c^∞((-1,1))`, `μ = (3/4)(1-x²)dx`) is formalised with every field proved, including density in `Lᵖ(μ)` (`goA₀_dense`). | `Instances/GegenbauerOpen/{Basic,Diffusion}.lean` |
| R22-E2-2 | INFO | `go_not_complete : ¬ goDiff.IsComplete` and `go_Γ₂_eq`, `goDiff_CD : GoCD ρ n` (`ρ ≤ 3`, `n ≥ 4`; `CD(3,4)` sharp in `n`): a weighted `DiffusionTriple` with `CD(n-1,n)` curvature that is not complete.  Unlike R21-1 the curvature is the genuine `n-1 = 3` Bochner one, `Γ₂ ≠ (Lf)²`. | `NotComplete.lean`, `Curvature.lean` |
| R22-E2-3 | INFO (scope) | S3 NOT done: whether `goDiff` extends to a `FullTriple` (F8: interior smoothness of `P_t f`; F10: ESA by limit-point at both endpoints, true by hand for `λ = 3/2`) is OPEN in Lean; GAPS row R21-4 stays open.  `GoCD` is a pointwise (not `FullTriple.CD`) statement. | this Status |

### Import lines for `MarkovTriple.lean` (not edited by me)
```
import MarkovTriple.BGL.Instances.GegenbauerOpen.Basic
import MarkovTriple.BGL.Instances.GegenbauerOpen.Diffusion
import MarkovTriple.BGL.Instances.GegenbauerOpen.NotComplete
import MarkovTriple.BGL.Instances.GegenbauerOpen.Curvature
import MarkovTriple.BGL.Instances.GegenbauerOpen.AxiomCheckR22E2
```
and `frozen-manifest.json` has one `proposed` entry for this file.
