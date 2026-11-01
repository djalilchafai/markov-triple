# BGL-aligned frozen surface (`MarkovTriple/BGL/Frozen/`, namespace `MarkovTriple.BGL`)

Status: **proposed** (nothing approved). Book = Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators*, Ch. 3; labels D1–D9, S10–S11, F1–F10 are the book's (§3.4).  Paraphrases only.
The old surface (`MarkovTriple/Frozen/`) is untouched; the new one is parallel (`MarkovTriple.BGL`).

## Global conventions (deviations from / choices about the book text)

* **A.e. everywhere** for equations between functions (book: "equalities are understood μ-a.e.", Def. 3.1.3, §1.14): symmetry,
  bilinearity, `Γ(f,f) ≥ 0`, diffusion property, F2, F5, F6, F8, F9.  Membership statements (`Γ(f,g) ∈ 𝒜₀`, `L f ∈ 𝒜₀`, `L f ∈ 𝒜`) are literal.
  Integral identities (D5, D8, F7) are exact.  Alternative: pointwise (stronger, instances satisfy it).
* **`Γ` and `L` are honest total functions** `(E→ℝ)→(E→ℝ)→(E→ℝ)`, `(E→ℝ)→(E→ℝ)`, constrained only on `𝒜₀`.
  On `𝒜`, `Γ` is `DiffusionTriple.ΓA` defined by the formula (F4); there is no second field.
  `ΓA = Γ` a.e. on `𝒜₀` is a theorem (`ΓA_ae_eq`).
* **No axioms**; every analytic requirement is a field or a theorem.
* "Good measurable space" (D1: countable generation mod null sets, measure decomposition theorem): **not encoded**; no hypothesis
  below uses it (it is used in the book for kernels, Prop. 1.2.3).  OPEN: author decides whether to add a field (e.g. separability of `L²`).

## Field-by-field table

### DiffusionTriple (Defs 3.1.1, 3.1.3, 3.1.8; D1–D8) — `Frozen/DiffusionTriple.lean`

| Label | Lean | Choice / alternatives / worries |
|---|---|---|
| D1 σ-finite; probability if finite | `sigmaFinite`, `finite_prob : IsFiniteMeasure μ → IsProbabilityMeasure μ` | as requested.  Excludes `μ = 0`. |
| D2 bounded measurable | `measurable`, `bounded : ∃ C, ∀ x, |f x| ≤ C` | boundedness EVERYWHERE (book), not essential (old surface). |
| D2 algebra | `A₀ : NonUnitalSubalgebra ℝ (E→ℝ)` | the book says "algebra" and "vector space stable under products" and later says constants are not in `𝒜₀`: non-unital. |
| D2 dense in `Lᵖ`, 1≤p<∞ | `dense` (+ `memLp`) | `memLp : 𝒜₀ ⊂ Lᵖ` is implicit in the book (density in `Lᵖ` presupposes membership); for infinite `μ` boundedness does not give it. |
| D2 stable under smooth ψ, ψ(0)=0 | `comp_mem` | `ψ : (Fin k→ℝ)→ℝ`, `ContDiff ℝ ⊤`; includes `k=0`. |
| Def 3.1.1 exhaustion | `exhaustion : ∃ u, IsExhaustion μ A₀ u` (`Frozen/Exhaustion.lean`) | "increasing" read a.e. (alternative: pointwise).  Existential, as in the book. |
| D3 Γ: 𝒜₀×𝒜₀→𝒜₀ | `Γ_mem` | |
| D3 symmetric, bilinear | `Γ_symm`, `Γ_add`, `Γ_smul` (first variable; second by symmetry), a.e. | |
| D3 Γ(f,f)≥0 | `Γ_nonneg` (a.e.) | |
| D3 diffusion (3.1.2)/(3.4.1) | `diffusion` (a.e.) | `pderiv` is `fderiv` applied to a basis vector (junk 0 off differentiability; ψ smooth so no junk). |
| (3.1.1) fundamental identity | not a field | the book: follows from the diffusion property.  Theorem NOT yet proved (easy from `Γ_mul_left`, `ψ=x²`). |
| D4 continuity of `g↦∫Γ(f,g)` | not a field; theorem `DiffusionTriple.exists_bound_D4` (`BGL/Basic.lean`) | derived from D5, D6 by Cauchy–Schwarz, proved. |
| D5 L by ibp | `L`, `ibp : ∫ g Lf = −∫Γ(f,g)` | linearity of `L` (a.e.) is a theorem (`L_add_ae`, `L_smul_ae`); `L` is determined only a.e. by ibp + density. |
| D5 chain rule for `L` (3.1.8) | not a field | the book: "consequence".  NOT yet proved on `𝒜₀` for a bare `DiffusionTriple` (needs ibp, product rule with `ψ_i − ψ_i(0)`); for a `FullTriple` it is F6.  Proved: Leibniz rule `Γ_mul_left`, `L_mul_ae` (3.1.6 polarised). **OPEN: pending theorem; if the author prefers a field it would be one line.** |
| D6 | `L_mem` | |
| D8 | `integral_L` | field (not derivable). |
| D7 Dirichlet form/domain, `L` | `DiffusionTriple.formDomain`, `closedForm` (`Frozen/FormDomain.lean`), `generator` (`Frozen/Semigroup.lean`) | Friedrichs construction (`BGL/FormData.lean`, port of `Hilbert/TripleForm.lean`; well-definedness on a.e.-classes proved from ibp+Γ≥0).  The book's characterisation of `𝒟(L)` ("∃C, |ℰ(f,g)|≤C‖g‖ ∀g∈𝒟(ℰ)") is the standard characterisation of the Friedrichs domain: NOT stated as a theorem here.  `Γ` is not extended to `𝒟(ℰ)` in the surface (not needed: PI/LSI are stated on a class).  Proved: `generator_cls` (`𝒜₀⊂𝒟(L)`, `L` extends `L|𝒜₀`); self-adjointness via `Hilbert.FormData.generator_selfAdjoint`. |
| D9 semigroup | `DiffusionTriple.semigroup : ℝ≥0 → L²→L L²` | `P_t = e^{tL}` of the Friedrichs generator (`FormData.semigroup`).  Positivity/sub-Markov: theorems to prove later (old `Hilbert/SubMarkov.lean` ports); not fields. |

### StandardTriple (Def 3.1.15; S10, S11) — `Frozen/StandardTriple.lean`

| S10 ergodic | `ergodic : u∈D(L), Lu=0 → ∃c, u =ᵐ c` | the book's equivalent form (`f∈𝒟(ℰ)`, Γ(f)=0 ⇒ const) not stated (needs `Γ` on `𝒟(ℰ)`). |
| S11 conservative | `conservative : ∀ exhaustion u, ∀ t, P_t(u_n) → 1 a.e.` | universal over exhaustion sequences (so independence is built in).  The book's "P_t on bounded measurable functions" is encoded by this monotone-limit device (the book itself defines `1` through the exhaustion sequence, remark after Def. 3.1.9).  Independence ("for some" ⇔ "for every") is NOT proved: it needs positivity + sub-Markov of `P_t` (pending): for nonnegative sequences `u_n↑1`, `v_m↑1`: `P_t(v_m∧u_n) ≤ P_t u_n`, `v_m∧u_n →_n v_m` in L² (dominated), so `P_t v_m ≤ lim P_t u_n`; symmetric.  Sequences taking negative values: more work.  **Worry (not verifiable from the text):** the book does not say which exhaustion sequence is meant.  For a probability `μ` it is `P_t 1 = 1` (as `L²` classes; `u_n → 1` in L² by dominated convergence). |

### FullTriple (Defs 3.3.1, 3.3.7, 3.3.25; F1–F10) — `Frozen/FullTriple.lean`

| F? | Lean | Notes |
|---|---|---|
| 𝒜 algebra of measurable fns ⊃ 𝒜₀, constants | `A : Subalgebra ℝ (E→ℝ)` (unital), `A₀_le`, `A_measurable` | |
| F1 ideal | `ideal : f∈𝒜, h∈𝒜₀ → h*f ∈ 𝒜₀` | |
| F2 positivity detection | `pos_detect` | "positive `h`" read `0 ≤ᵐ h`; alternative: pointwise (that makes F2 stronger). |
| F3 | `A_comp` (all smooth ψ, no ψ(0)=0) | |
| F4 | `L_mem_A`; `Γ` := `ΓA` | "L extends L|𝒜₀" is built in (same function); `ΓA(f,g) ∈ 𝒜` derived (`ΓA_mem_A`); `ΓA(f,h)∈𝒜₀` for `h∈𝒜₀` derived from F1 (`ΓA_mem_A₀`). |
| F5 | `ΓA_nonneg` (a.e.) | |
| F6 | `diffusion_Γ_A` (g∈𝒜), `diffusion_L_A` | a.e.; ψ smooth, no vanishing condition.  `k=0` gives `L1=0`, `ΓA(1,·)=0`; linearity of `L` on `𝒜` follows (ψ=x+y, cx). |
| F7 | `ibp_A : ∫ΓA(f,g) = −∫gLf ∧ ∫ΓA(f,g) = −∫fLg` | equalities of Bochner integrals only; integrability of all three terms is the theorem `FullTriple.integrable_F7` (from F1 + memLp), so no junk-value loophole. |
| F8 | `semigroup_A` | as an `L²`-class: `P_t[f]` has a representative in `𝒜`.  (Book: `P_t f ∈ 𝒜`, f a class.) |
| F9 connexity (Def 3.3.7) | `connected` | hypothesis and conclusion a.e. (`Γ(f)=0` a.e. ⇒ `f` a.e. constant). |
| F10 ESA (Def 3.1.10) | `esa` | "core" form: every `u∈𝒟(L)` is the `L²`-limit of classes `a_n∈𝒜₀` with `L a_n → Lu`.  The equivalence with `𝒟(L)=𝒟(L*)` (stated by the book) is not proved; the old range-criterion form is replaced. |
| Def 3.3.26 | `CompactTriple` (`A_eq : f∈𝒜 ↔ f∈𝒜₀`) | the book says ESA is automatic; it stays a (redundant) field of `FullTriple`. |

### Γ₂, CD, functional inequalities

* `DiffusionTriple.Γ₂ T f g` (Def 3.3.12) uses `ΓA` and `L`; `Γ₂(f) = Γ₂ f f`.
* `FullTriple.CD ρ n` (Def 3.3.14): `1 ≤ n ∧ ∀ f∈𝒜, a.e. ρ ΓA f f + (n⁻¹).toReal (Lf)² ≤ Γ₂ f f`; `n=∞` ⇒ no term; `n<1` excluded.  On ALL of `𝒜` (old split `CD`/`CDFull` removed).
* `PoincareIneq μ Γ 𝒞 C` (Def 4.2.1): `IsProbabilityMeasure μ ∧ 0<C ∧ ∀f∈𝒞, Var f ≤ C ℰ(f)`.
  `LogSobolevIneq μ Γ 𝒞 C D` (Def 5.1.1): `…∧ 0<C ∧ 0≤D ∧ ∀f∈𝒞, Ent(f²) ≤ 2Cℰ(f) + D∫f²` — **worry**: the text extraction lost the parentheses; the grouping `2C ℰ(f) + D ∫f²` (D not multiplied by 2C) is inferred from (5.1.4) (`C/2 ∫Γ(f)/f + D∫f` with f→f²).  `Ent`, `fisherInfo`, `energy`, `dirichletForm` generic in `(μ,Γ)`.
  The books states PI/LS on `𝒟(ℰ)`; here the class `𝒞` is a parameter (book: "enough on a dense family such as 𝒜₀").  Instantiate with `T.A₀` and `T.Γ`, or `T.A` with `T.ΓA`.

## Removed from the old surface (not in the book)
`ibp_AA`, `IsSemigroupOf` (replaced by the construction `semigroup`; its characterisation as theorem later), `BEStable`, split CD, `esa` range-criterion, `semigroup_stable` quantifying over all `P`.

## Imports / layering
`Frozen/Semigroup.lean` imports `BGL/FormData.lean` (non-frozen, proofs) and `Hilbert/Existence` (generic Friedrichs).  `Frozen/Classes.lean` defines the class maps `cls`, `Lcls` used by S11/F8/F10.

## Proved so far outside the frozen files (`BGL/`)
`Basic` (D4, `L_add_ae`, `L_smul_ae`, `ae_zero_of_orth`), `FormData` (Friedrichs form data, well-definedness), `SemigroupLemmas` (`generator_cls`, `semigroup_cls_of_L_zero`), `Consistency` (Leibniz rule for Γ, `L_mul_ae`, `ΓA_ae_eq`), `FullBasic` (`ΓA_mem_A`, `ΓA_mem_A₀`, `integrable_F7`).

## Still to prove (not fields; none blocking the surface)
chain rule for `L` on `𝒜₀` (bare diffusion triple); fundamental identity (3.1.1); positivity & sub-Markov of `semigroup`; independence of the exhaustion sequence in S11; equivalence `esa ⇔ D(L)=D(L*)`; characterisation of `𝒟(L)` (D7); equivalence of S10 with its `Γ`-form; ESA automatic when `𝒜=𝒜₀`.
