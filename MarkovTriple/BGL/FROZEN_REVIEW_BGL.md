# BGL-aligned frozen surface (`MarkovTriple/BGL/Frozen/`, namespace `MarkovTriple.BGL`)

Status: **proposed** (nothing approved).  Updated after the realignment round of audit items M1, M2, M3, L1 (see the section "Round 2 changes" at the end). Book = Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
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
| (3.1.1) fundamental identity | not a field; theorem `DiffusionTriple.fundamental_identity` (+ `_ae`) in `BGL/Calculus/Identities.lean` | proved: `∫Γ(f²,g) + 2∫gΓ(f) = 2∫Γ(fg,f)` (and a.e. before integration), from the Leibniz rule + symmetry. |
| D4 continuity of `g↦∫Γ(f,g)` | not a field; theorem `DiffusionTriple.exists_bound_D4` (`BGL/Basic.lean`) | derived from D5, D6 by Cauchy–Schwarz, proved. |
| D5 L by ibp | `L`, `ibp : ∫ g Lf = −∫Γ(f,g)` | linearity of `L` (a.e.) is a theorem (`L_add_ae`, `L_smul_ae`); `L` is determined only a.e. by ibp + density. |
| D5 chain rule for `L` (3.1.8) | not a field; theorem `DiffusionTriple.chain_rule_L` (`BGL/Calculus/Identities.lean`) | PROVED on `𝒜₀` for a bare `DiffusionTriple` (a.e.; exactly the shape of F6 with `Γ` for `ΓA`): both sides lie in `𝒜₀` (via `ψᵢ − ψᵢ(0)` and `comp_mem`), have the same integral against every `g ∈ 𝒜₀` (ibp, the diffusion property for `ψ`, Leibniz on `(ψᵢ−ψᵢ(0))(f)·g`), so agree a.e. by density.  Also proved earlier: Leibniz rule `Γ_mul_left`, `L_mul_ae` (3.1.6 polarised).  No field needed. |
| D6 | `L_mem` | |
| D8 | `integral_L` | field (not derivable). |
| D7 Dirichlet form/domain, `L` | `DiffusionTriple.formDomain`, `closedForm` (`Frozen/FormDomain.lean`), `generator` (`Frozen/Semigroup.lean`) | Friedrichs construction (`BGL/FormData.lean`, port of `Hilbert/TripleForm.lean`; well-definedness on a.e.-classes proved from ibp+Γ≥0).  The book's characterisation of `𝒟(L)` is now a THEOREM, `DiffusionTriple.generator_iff_form` (`BGL/Semigroup/Characterization.lean`): `u ∈ 𝒟(L) ∧ L u = y ⇔ u ∈ 𝒟(ℰ) ∧ ∀ v ∈ 𝒟(ℰ), ℰ(u,v) = −⟪y,v⟫` (equivalent by Riesz to the bounded-functional form).  `𝒟(ℰ)` is the completion of `𝒜₀`: `formDomain_approx` (`BGL/Calculus/Density.lean`).  `Γ` is not extended to `𝒟(ℰ)` in the surface (not needed: PI/LSI are stated on a class).  Proved: `generator_cls` (`𝒜₀⊂𝒟(L)`, `L` extends `L|𝒜₀`); self-adjointness via `Hilbert.FormData.generator_selfAdjoint`. |
| D9 semigroup | `DiffusionTriple.semigroup : ℝ≥0 → L²→L L²` | `P_t = e^{tL}` of the Friedrichs generator (`FormData.semigroup`).  PROVED (`BGL/Semigroup/Markov.lean`, port of the old Beurling–Deny / MarkovCriterion / SubMarkov): `isMarkovianForm` (first Beurling–Deny, via `ψ_δ = √(t²+δ²)−δ`), `semigroup_nonneg` (positivity), `isClipForm` + `semigroup_le_one` (sub-Markov, via smooth truncations of `t ∧ c`), `norm_semigroup_le` (`L²`-contractivity); all for a bare `DiffusionTriple`, no extra hypothesis. |

### StandardTriple (Def 3.1.15; S10, S11) — `Frozen/StandardTriple.lean`

| S10 ergodic | `ergodic : u∈D(L), Lu=0 → ∃c, u =ᵐ c` | the book's second form (`f∈𝒟(ℰ)`, `Γ(f)=0` ⇒ const) is the theorem `DiffusionTriple.ergodic_iff_energy`: S10 ⇔ (`u ∈ 𝒟(ℰ)`, `ℰ(u,u)=0` ⇒ const).  `Γ` is not extended to `𝒟(ℰ)` in the surface; `ℰ(u)=∫Γ(u)` is the closed form (for `u ∈ 𝒜₀`: `energy_zero_iff`: `ℰ(u)=0 ⇔ Γ(u)=0` a.e.).  Corollary `StandardTriple.energy_zero_const`. |
| S11 conservative | `conservative : ∀ exhaustion u (u_n ≥ 0 a.e.), ∀ t, P_t(u_n) → 1 a.e.` | **CHANGED (M3)**: the quantifier ranges over exhaustion sequences with `0 ≤ u_n` a.e.  Independence of the exhaustion sequence is now PROVED: `DiffusionTriple.conservative_transfer` (`BGL/Semigroup/Conservative.lean`): S11 for ONE exhaustion sequence gives S11 for EVERY exhaustion sequence, signed or not (`StandardTriple.conservative_all`); nonnegative sequences exist (`exists_nonneg_exhaustion`, `ψ` = `Real.smoothTransition`), so the restriction loses nothing and the field is weaker (easier to verify) but equivalent.  Reading was NOT wrong (the signed reading is a theorem).  Proof of independence: `n ↦ P_t u_n` is a.e. increasing and `≤ 1` (positivity, sub-Markov), `(v_m − u_n)⁺ → 0` in `L²` (dominated convergence), `P_t` is positive and an `L²` contraction.  The 'splitting off u_0' is not needed.  For finite `μ`: `conservative_iff_semigroup_one`: S11 ⇔ `P_t[1] = [1]` in `L²`.  Mass conservation `StandardTriple.integral_semigroup`: `h ∈ L¹∩L²` ⇒ `P_t h ∈ L¹`, `∫P_t h = ∫h`; `integral_semigroup_of_one` (finite `μ`).  (Old text:) universal over exhaustion sequences (so independence is built in).  The book's "P_t on bounded measurable functions" is encoded by this monotone-limit device (the book itself defines `1` through the exhaustion sequence, remark after Def. 3.1.9).  (Old remark on independence is superseded: proved, see above.)  **Worry (not verifiable from the text):** the book does not say which exhaustion sequence is meant.  For a probability `μ` it is `P_t 1 = 1` (as `L²` classes; `u_n → 1` in L² by dominated convergence). |

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
| Def 3.3.26 | `CompactTriple` (`A_eq : f∈𝒜 ↔ f∈𝒜₀`) | the book says ESA is automatic; it stays a (redundant) field of `FullTriple`; PROVED redundant: `CompactTriple.esa_auto` (`BGL/Semigroup/ESA.lean`), from F8 + `𝒜=𝒜₀` (a dense `P_t`-invariant domain is a core; `core_of_invariant`). |

### Γ₂, CD, functional inequalities

* `DiffusionTriple.Γ₂ T f g` (Def 3.3.12) uses `ΓA` and `L`; `Γ₂(f) = Γ₂ f f`.
* `FullTriple.CD ρ n` (Def 3.3.14): `1 ≤ n ∧ ∀ f∈𝒜, a.e. ρ ΓA f f + (n⁻¹).toReal (Lf)² ≤ Γ₂ f f`; `n=∞` ⇒ no term; `n<1` excluded.  On ALL of `𝒜` (old split `CD`/`CDFull` removed).
* `PoincareIneq μ Γ 𝒞 C` (Def 4.2.1): `IsProbabilityMeasure μ ∧ 0<C ∧ ∀f∈𝒞, Var f ≤ C ℰ(f)`.
  `LogSobolevIneq μ Γ 𝒞 C D` (Def 5.1.1): `…∧ 0<C ∧ 0≤D ∧ ∀f∈𝒞, Ent(f²) ≤ 2Cℰ(f) + D∫f²` — **worry**: the text extraction lost the parentheses; the grouping `2C ℰ(f) + D ∫f²` (D not multiplied by 2C) is inferred from (5.1.4) (`C/2 ∫Γ(f)/f + D∫f` with f→f²).  `Ent`, `fisherInfo`, `energy`, `dirichletForm` generic in `(μ,Γ)`.
  The books states PI/LS on `𝒟(ℰ)`; here the class `𝒞` is a parameter (book: "enough on a dense family such as 𝒜₀").  **ADDED (M2)**: triple-bound versions next to the generic ones: `DiffusionTriple.ℰ (f g : T.A₀)` (`Frozen/Energy.lean`), `DiffusionTriple.PI T C := PoincareIneq T.μ T.Γ T.A₀ C` (`Frozen/Poincare.lean`), `DiffusionTriple.LS T C D := LogSobolevIneq T.μ T.Γ T.A₀ C D` (`Frozen/LSI.lean`); the class is the triple's own `𝒜₀` (bounded: no Bochner junk, `integrable_sq_mul_log_sq`; never `𝒜`).  `𝒜₀` is dense in `𝒟(ℰ)` (`formDomain_approx`: `L²` convergence + `ℰ(u−a_n) → 0` + `ℰ(a_n) → ℰ(u)`), and the inequalities extend: `DiffusionTriple.PI.extend`, `DiffusionTriple.LS.extend` (`BGL/Calculus/Density.lean`, `LSIExtend.lean`; the latter also proves integrability of `u² log u²` on `𝒟(ℰ)`).  The generic versions remain (for `T.A`, `ΓA`).

## Removed from the old surface (not in the book)
`ibp_AA`, `IsSemigroupOf` (replaced by the construction `semigroup`; its characterisation as theorem later), `BEStable`, split CD, `esa` range-criterion, `semigroup_stable` quantifying over all `P`.

## Imports / layering
`Frozen/Semigroup.lean` imports `BGL/FormData.lean` (non-frozen, proofs) and `Hilbert/Existence` (generic Friedrichs).  `Frozen/Classes.lean` defines the class maps `cls`, `Lcls` used by S11/F8/F10.

## Proved so far outside the frozen files (`BGL/`)
`Basic` (D4, `L_add_ae`, `L_smul_ae`, `ae_zero_of_orth`), `FormData` (Friedrichs form data, well-definedness), `SemigroupLemmas` (`generator_cls`, `semigroup_cls_of_L_zero`), `Consistency` (Leibniz rule for Γ, `L_mul_ae`, `ΓA_ae_eq`), `FullBasic` (`ΓA_mem_A`, `ΓA_mem_A₀`, `integrable_F7`), and, in round 2:
* `Calculus/Identities.lean`: `fundamental_identity(_ae)` (3.1.1), `chain_rule_L` (3.1.8) on `𝒜₀`.
* `Semigroup/Markov.lean`: `isMarkovianForm`, `semigroup_nonneg`, `isClipForm`, `resolvent_le_one`, `semigroup_le_one`, contractivity.
* `Semigroup/Conservative.lean`: monotonicity/boundedness of `P_t u_n`, `comparison`, `conservative_transfer`, `StandardTriple.conservative_all`, `exists_nonneg_exhaustion`.
* `Semigroup/Mass.lean`: `conservative_iff_semigroup_one` (finite `μ`), `integral_semigroup_of_one`, `StandardTriple.integral_semigroup` (`∫P_t h = ∫h`, `h ∈ L¹∩L²`).
* `Semigroup/Characterization.lean`: `generator_iff_form`, `ergodic_iff_energy`, `energy_zero_iff`, `closedForm_cls`.
* `Calculus/Density.lean`, `Calculus/LSIExtend.lean`: `formDomain_approx`, `PI.extend`, `LS.extend`, `integrable_sq_mul_log_sq`.
* `Semigroup/ESA.lean`: `core_of_invariant`, `CompactTriple.esa_auto`.
All with only `propext`, `Classical.choice`, `Quot.sound` (`BGL/AxiomCheck.lean`).

## Still to prove / open (none blocking the surface)
* equivalence `esa ⇔ D(L)=D(L*)` (note: `generator` is self-adjoint, so the book's ESA is exactly the core property, which IS the `esa` field; `D(L)=D(L*)` for the closure of `L|𝒜₀` is the same statement) — not written out.
* extension of `Γ` itself to `𝒟(ℰ)` (D4 of the book): only the closed form `ℰ` on `𝒟(ℰ)` is available (this suffices for S10/PI/LS).
* "good measurable space" (D1) not encoded (unchanged).
* mass conservation for infinite `μ` needs S11 (a field) — proved from it; not derivable for a bare `DiffusionTriple` (Dirichlet counterexample).
* `Γ₂`/CD consequences (Props 3.3.16–17, Thm 3.3.18, 3.3.23) and instances beyond `Unit` (circle `FullTriple`, OU, Lebesgue) — later stages.

## Round 2 changes (audit items M1, M2, M3, L1)

**M1 (fence).**  `scripts/check_frozen.py` now reads a second list `"fenced"` in `frozen-manifest.json`: non-frozen files whose *definitions* the frozen `semigroup`/`generator`/`formDomain`/`closedForm` unfold to, hashed like the frozen ones: `BGL/FormData.lean`, `BGL/Basic.lean`, `Hilbert/{Friedrichs, Resolvent, Generator, SemigroupDeriv, SemigroupSmoothing, CfcSemigroup, Complexify, ResolventGenerator, Existence, SpectralGap}.lean`.  The script also computes the transitive project-import closure of every `BGL/Frozen/*.lean` and reports `UNFENCED dependency` for any file that is neither frozen nor fenced, so a new dependency cannot sneak in.  In addition the characterisation theorem `generator_iff_form` (+ `generator_cls`, `closedForm_cls`, `formDomain_approx`) is proved (not frozen), so the meaning of the definitions is pinned down by theorems and not only by hashes (cheapest sound option: fence + theorem; no frozen statement was added for it).  To change a fenced file: edit, then `python3 scripts/check_frozen.py --update`.

**M2.**  See the PI/LS paragraph above.

**M3.**  `StandardTriple.conservative`: old `∀ u (hu : IsExhaustion μ A₀ u) (t : ℝ≥0), ∀ᵐ x, Tendsto (…) atTop (𝓝 1)`; new `∀ u (hu : IsExhaustion μ A₀ u), (∀ n, 0 ≤ᵐ[μ] u n) → ∀ (t : ℝ≥0), ∀ᵐ x, Tendsto (…) atTop (𝓝 1)`.  The signed statement is the theorem `StandardTriple.conservative_all`.

**L1.**  Fundamental identity, chain rule, positivity, sub-Markov, contractivity, independence, `P_t 1 = 1` (finite `μ`), mass conservation, S10 second form, ESA for compact triples: all proved (see "Proved so far").

**Frozen statements changed in round 2 (old → new).**
1. `Frozen/StandardTriple.lean`: S11 `conservative` (M3 above) and its docstring.
2. `Frozen/Energy.lean`: added `import …Frozen.DiffusionTriple` and the definition `DiffusionTriple.ℰ` (new; no old statement changed).
3. `Frozen/Poincare.lean`: added import and `DiffusionTriple.PI` (new).
4. `Frozen/LSI.lean`: added import and `DiffusionTriple.LS` (new).
No other frozen file changed; the manifest hashes were updated with `--update`.
