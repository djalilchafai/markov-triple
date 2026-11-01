# Hostile audit of the BGL frozen surface (`MarkovTriple/BGL/Frozen/`)

Auditor method: Lean files read first, then `FROZEN_REVIEW_BGL.md`; book (BGL Ch. 3 summary §3.4, Defs 3.1.1, 3.1.9-3.1.12, 3.3.14, 4.2.1, 5.1.1) paraphrased only.
Machine evidence: `BGL/Audit/AxiomWalk.lean` (168 constants under `MarkovTriple.BGL.*`: only propext/choice/Quot.sound, 0 sorry), `BGL/Audit/Probes.lean` (compiles). `scripts/check_frozen.py` = OK. Grep for sorry/axiom/native_decide/unsafe/opaque/implemented_by/choose in `BGL/` (outside Audit): no hits.
Verdict: no refutation found; surface is faithful modulo the items below. No field is contradictory by my sketches (circle, Lebesgue on R, OU all appear to satisfy every field); however only `Unit` is proved Full.

## Findings (severity, location, issue, fix)

### M1 (MEDIUM) Meaning-bearing definitions live outside the frozen perimeter
`Frozen/Semigroup.lean:21-32` defines `semigroup`/`generator` as `(formData T).semigroup/.generator`; `formData` is in `BGL/FormData.lean:184` (unfrozen) and `Q`, `E`, `R`, `semigroup`, `generator` are in `Hilbert/Friedrichs.lean:150-168`, `Hilbert/Resolvent.lean:39`, `Hilbert/Generator.lean:59` (none in `frozen-manifest.json`; the manifest lists only `BGL/Frozen/*` and the OLD `Frozen/*`). `check_frozen.py` hashes only listed files, so editing `formData` (e.g. a different domain `D`, or another self-adjoint extension) silently changes S10, S11, F8, F10 and `formDomain` while the hashes stay OK. Not exploitable today (proved: `generator_extends`, `generator_selfAdjoint`, `isGeneratorOf_generator`), but a self-adjoint extension of `-A` is NOT unique without ESA, so these theorems do not pin it down as the Friedrichs one.
Fix: add `BGL/FormData.lean`, `Hilbert/Friedrichs.lean`, `Hilbert/Resolvent.lean`, `Hilbert/Generator.lean` (+ `CfcSemigroup` def part) to the manifest, or freeze a characterisation theorem: `D(G) ⊆ formDomain` and `∀ u ∈ D(G), v ∈ formDomain, closedForm u v = -⟪G u, v⟫`.

### M2 (MEDIUM) PI / LSI / energy are generic in (μ, Γ, 𝒞): not tied to a triple, vacuous or junk
`Poincare.lean:17`, `LSI.lean:17`, `Energy.lean:16`.
* `PoincareIneq μ Γ ∅ C` and `LogSobolevIneq μ Γ ∅ C D` hold for every probability μ and any Γ (`Audit/Probes.lean`: `pi_empty`, `lsi_empty`). The book states them on `D(E)` (dense family suffices); the Lean statement does not force `𝒞` dense in `formDomain`.
* Bochner junk: `energy_junk` / `pi_fails_of_junk`: if `Γ f f` is not integrable, `energy = 0`, so `PoincareIneq μ T.ΓA T.A C` is FALSE for any full triple having a nonconstant L² function of infinite energy in `𝒜` (e.g. OU, `f = e^{x²/4}/(1+x²)`, which is in C^∞ and L²(γ) with non-integrable `f'^2`). With `𝒞 = T.A₀` there is no junk (everything bounded, in L¹). `Ent`/`∫f²` junk likewise outside `A₀`. `variance` of f ∉ L² is 0 (Mathlib), harmless.
* Both are stated for arbitrary Γ: a user can pass an unrelated Γ.
Fix (non-breaking): add triple-bound versions `DiffusionTriple.PI T C := PoincareIneq T.μ T.Γ T.A₀ C` / `.LS`, and a lemma (stage Poincaré/LSI) that `A₀` is dense in `formDomain` so the book's D(E)-form follows; document that `𝒞` must be `A₀` (never `A`).

### M3 (MEDIUM) S11 encoding: strongest reading, equivalence with `P_t 1 = 1` needs positivity
`StandardTriple.lean:32-34`. Encoding: every exhaustion sequence u (a.e. increasing, a.e. limit 1, terms in `A₀`, possibly negative: `Probes` example with `u₀ = -5`) satisfies `P_t u_n → 1` a.e. Assessment:
* Right idea (the book defines "1" through the exhaustion sequence; `P_t` on bounded measurable functions). Satisfiable: Lebesgue on R / OU: `u_n ≥ u_0`, `P_t u_n = P_t u_0 + P_t(u_n - u_0)`, monotone convergence and `P_t 1 = 1` (Gaussian kernel). Not satisfied by killed BM: `A₀ = C_c^∞(0,1)`, Lebesgue on (0,1) (probability), Friedrichs generator = Dirichlet Laplacian, `P_t u_n → P_t 1 < 1`; a conservative-for-L² formulation `P_t 1 = 1` would see the same. Also fails for any explosive 1-d diffusion.
* For finite μ it implies `P_t 1 = 1` in L² (L² limit = a.e. limit); converse requires `P_t` positivity preserving (then `P_t u_n` is a.e. increasing so a.e. limit exists = L² limit). Everything beyond that (independence of u, infinite μ: `∫ P_t h = ∫ h` for `h ∈ L¹∩L²`, `h ≥ 0`) is a theorem to be proved from Beurling-Deny/positivity; it is not in the surface. Negative-valued sequences add a small decomposition `u_n = u_0 + (u_n - u_0)`.
* Also note the book's Thm 3.3.23 (mass conservation from CD+ESA) becomes redundant for a Standard/Full triple since S11 is a field, as in the book's own Def 3.3.25.
Option: restrict the quantifier to `0 ≤ᵐ u_n` (equivalent in all intended cases, simpler to prove and to use); keep as is if the author wants maximal strength.

### L1 (LOW-MED) Pending theorems that the surface relies on being derivable
(3.1.1) fundamental identity, chain rule (3.1.8) for `L` on `A₀` for a bare `DiffusionTriple`, `ΓA=Γ` a.e. on `A₀` (proved), D4 (proved). I checked the chain-rule derivation sketch (ibp + diffusion with `ψ_i - ψ_i(0)`, product rule `Γ(f_i, g h)`, density): it works. Fundamental identity: from diffusion with `ψ(x,y)=x y`, `x²`: fine. Not a field is OK, but they are needed by Prop 3.3.16-17 and Thm 3.3.18 on `A₀`.

### L2 (LOW) Omissions / deviations (all documented in the review, confirmed)
* D1 "good measurable space": not encoded (no hypothesis uses it). LOW; add if kernels/Prop 1.2.3 are used (e.g. representing `P_t` by a kernel for positivity of conservative statements).
* D4 "Γ extended to D(E)" and S10's second form (`f ∈ D(E)`, `Γ(f)=0` ⇒ const): absent; the equivalence is a theorem to prove (needed to use S10 with `Γ`).
* CD (Def 3.3.14) is stated only for `FullTriple` on all of `𝒜` (the book states it on `A₀` for a Standard triple and extends to `A` by Remark 3.3.15). Stronger-looking, equivalent by the Remark; no CD for `StandardTriple`. `n ∈ [1,∞]`, `(n⁻¹).toReal`, `∞⁻¹=0`: faithful, no junk (n ≥ 1 so `n⁻¹` finite).
* `IsExhaustion` increasing/converging a.e.: fine (book convention).
* `Γ`,`L` total functions constrained a.e. except `∈ A₀`/`∈ A` memberships (literal). Consequence: on `𝒜` the structure pins `L` only a.e. modulo functions of `𝒜`; ok for continuous instances (a.e. equal continuous functions are equal when μ has full support). For instances where μ lacks full support, the literal memberships plus a.e. equations are still consistent (take representatives).
* `ESA` is a field of `CompactTriple` (redundant, as book says automatic): fine.

### Field-by-field faithfulness (checked against the book)
* D1-D3, D5-D8: faithful. `bounded` everywhere (book), `memLp` an extra but implicit hypothesis (needed for density to make sense when μ infinite) - justified. `dense` binder `∀ _ : Fact (1 ≤ p)` equivalent to `1 ≤ p`. `ContDiff ℝ (⊤:ℕ∞)` is C^∞ (not analytic). `comp_mem` k=0 gives `0 ∈ A₀` only.
* D7: `formDomain = Q` (completion of `A₀` for `(‖f‖²+ℰ(f))^½`, injectivity proved), `closedForm = E1 - ⟪,⟫`; `generator` = Friedrichs, whose domain equals the book's `{f ∈ D(E): |ℰ(f,g)| ≤ C‖g‖}`. OK (modulo M1).
* S10: `u ∈ D(L)`, `Lu=0` ⇒ a.e. constant; for infinite μ the constant must be 0 automatically (`Lp` membership). Faithful.
* F1 `h*f ∈ A₀`: faithful. F2: a.e. reading, `∫ h f` is a genuine integral (`h f ∈ A₀ ⊂ L¹` by F1) - no junk. F3, F4 (`L_mem_A`; Γ by formula `ΓA`), F5, F6 (both formulas, all smooth ψ incl. k=0, `pderiv₂ ψ i j = ∂_j ∂_i ψ`): faithful.
* F7: all three terms integrable by F1 (`g·Lf`: `g∈A₀`, `Lf∈A`; `f·Lg`: `Lg∈A₀`, `f∈A`; `L(fg)`: `fg∈A₀`), proved as `integrable_F7`; so not satisfied by junk 0=0. Together the two equalities give `∫L(fg)=0` and `∫fLg = ∫gLf`.
* F8 (book: `f ∈ A₀`): as L²-class with a representative in `A`: faithful. F9: faithful (a.e.). F10: "A₀ is a core for the Friedrichs generator" is equivalent to the book's ESA (closure of `L|A₀` is self-adjoint iff it equals the unique/Friedrichs extension); neither trivially true (fails for `C_c^∞(0,1)` Dirichlet Laplacian: `H²∩H¹₀` is strictly larger than the `H²₀` closure) nor false (`trivialCompact`; BM on R and OU on `C_c^∞`; circle).
* PI: `Var ≤ C ℰ` and LS(C,D): `Ent(f²) ≤ 2C ℰ(f) + D ∫f²` match Defs 4.2.1 and 5.1.1 exactly (review's "worry" is resolved: the book text has `2C ℰ(f) + D ∫ f²` with D multiplying only `∫f²`). `Ent` uses `Real.log 0 = 0` (correct convention for x log x).

### Non-vacuity (sketches; no hidden contradiction found)
* Circle (Haar probability, `A₀=A=C^∞`, `L=f''`): F1 trivial, F2 (continuous f, positive test functions), F3, F5-F7 classical, F8 (`P_t` Fourier multiplier, `A=A₀`), F9 (`f'²=0`), F10 (A₀ contains all trigonometric polynomials; `A₀ ⊂ D(L)` and the Friedrichs generator is the closure of `f''` on trig polynomials; core), S10 (kernel = constants), S11 (`u_n=1`). `exhaustion` u_n=1 is consistent with a finite probability measure (`finite_prob` fine; `Unit` already proves this).
* Lebesgue on R (`A₀=C_c^∞`, `A=C^∞`): `μ` infinite so `finite_prob` vacuous; exhaustion by cutoffs; boundedness everywhere (compact support) and `L¹/L²` membership OK; F1 `C_c^∞·C^∞ ⊂ C_c^∞`; F7 integration by parts with compact support; F8 heat semigroup keeps C^∞; F10 (`-Δ` ESA on `C_c^∞(ℝ)`); S10 (`Lu=0`, `u∈L²` ⇒ u=0); S11 as above. OU similar (Mehler; Hermite functions core).
* Instances requiring more than `Unit` for S10-S11-F fields are NOT yet proved in Lean: `BGL/Sanity/Circle.lean` gives only D1-D8; hence "full" non-vacuity with Γ ≠ 0 is evidenced by sketch only. Top priority for next stage.
* No contradictions of the kind: exhaustion vs finite μ (u_n=1 works if constants ∈ A₀, else cutoffs), everywhere-bounded vs a.e. fields (fields never demand pointwise equalities of `Γ`,`L` outside memberships), ε-null junk (a.e. equalities cannot produce inconsistency; `ΓA` is a pointwise formula of the field `L`, F9/F5/CD are only a.e. statements about it, `L f ∈ A` literal).

### Junk summary
Bochner: `energy`, `Ent`, `fisherInfo`, F2/F7 integrals (F2, F7 safe by F1+`memLp`; D5/D8/Γ integrals safe by `memLp`; PI/LSI unsafe off `A₀`, see M2). `ENNReal.toReal`: only `(n⁻¹).toReal` with `1 ≤ n`: safe. No `Classical.choose` in frozen defs (grep). `pderiv` junk only off differentiability (ψ smooth ⇒ none). Universe: `E : Type*` everywhere; no issue. `Fisher.IsFisherAdmissible` is the right guard (`x/0=0`).

### Tooling
`scripts/check_frozen.py` scans `MarkovTriple/BGL/Frozen` for UNLISTED files, and hashes all 17 listed BGL entries (OK now). It does not cover transitive non-frozen dependencies (M1) nor the `Audit/` files (intended). `BGL/Audit/` is not imported by `MarkovTriple.lean`.

## What the next stages need from the surface (priority)
1. Circle: complete the `CompactTriple` instance (S10, S11, F1-F10) to test non-vacuity with Γ ≠ 0 (A=A₀=C^∞(T): F8 needs P_t f ∈ A₀: Fourier/Mehler; F10 `A₀` core).
2. Positivity preserving + sub-Markov of `semigroup` (Beurling-Deny, port `Hilbert/BeurlingDeny`, `SubMarkov`, `MarkovCriterion`) - needed for: independence of the exhaustion sequence in S11, the a.e. monotonicity of `P_t u_n`, Props 3.3.16-3.3.17 (`P_t` maps to `A`, Γ commutation), mass conservation. Needs `cls`/`Lcls` lemmas (`generator_cls`, `semigroup_cls_of_L_zero` exist) and lemma `A₀ ⊂ D(L)`.
3. Gradient bound (Thm 3.3.18): needs Γ(P_t f) on `A` via `ΓA`, F8 (`P_t f ∈ A`), F6, F7 (extended ibp), F1 (to integrate against `A₀`), `ΓA_ae_eq`, F2 (to pass from integrals to a.e. inequalities - the reason F2 is a field), CD on `A`, and the derivative `d/ds P_s(Γ(P_{t-s}f))` which needs a semigroup differentiation lemma on `A₀` classes (`Hilbert/SemigroupDeriv`) plus ESA (F10) to differentiate in the graph norm.
4. Mass conservation (Thm 3.3.23): S11 is a field, so proof is redundant for Full triples; but D(L)-form and Prop 3.1.13 (ergodic limits) use S10/S11; need `∫ P_t h = ∫ h` for `h ∈ L¹∩L²` (extend S11 to this via duality: needs the independence + positivity of item 2).
5. Instances (OU, Lebesgue, spheres): need F10 by a criterion (e.g. CD + completeness or Hermite basis), exhaustion, and S11 via explicit kernel or the 3.3.23 route; for infinite measure prove S11 with sign-indefinite sequences (decomposition `u_0 + (u_n - u_0)`), or restrict (M3).
6. Poincaré/LSI: use triple-bound statements on `A₀` (M2), prove density of `A₀` in `formDomain`; need (3.1.1)/chain rule (L1) and `Γ(√h)` identities for Fisher information; `Ent`/`variance` lemmas with `MemLp` side conditions to avoid junk; `A₀` bounded ⇒ `f² log f²` integrable when `μ` is a probability.
7. Freeze/fence the unfrozen definitions (M1) before building more on top.

## Files created by this audit
`BGL/Audit/AxiomWalk.lean`, `BGL/Audit/Probes.lean`, this file. Nothing else modified.
