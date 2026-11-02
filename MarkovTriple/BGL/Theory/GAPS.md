# BGL/Theory: what is proved, what is conditional, exact missing lemmas

Book = Bakry–Gentil–Ledoux, Ch. 3–5 (paraphrases only).  Hypotheses used: only F1–F10 of the frozen
`FullTriple`, plus (where stated) a *named `Prop` structure* of regularity hypotheses.  No axiom,
no `sorry`.  `Theory/Tests.lean` proves that each regularity structure holds for the trivial
compact triple (so none is contradictory or vacuous there).

## Proved unconditionally

| File | Statement |
|---|---|
| `Gamma2Integral` | (3.3.8) on `𝒜₀`: `∫Γ₂(f) = ∫(Lf)²` (`integral_Γ₂`); integrated CD on `𝒜₀` (`integral_CD`, `integral_CD_infty`); **extension to `𝒟(L)` by ESA** of the integrated CD: `ρ ℰ(u) + n⁻¹‖Lu‖² ≤ ‖Lu‖²`, `ℰ(u) = -⟪Lu,u⟫` (`CD_integrated_domain`, `CD_form_domain`). This is Prop. 3.3.16 (i)–(ii) in integrated form. |
| `ESAOne` | **Finite μ: ESA ⇒ `1 ∈ 𝒟(L)`, `L1 = 0`, `P_t 1 = 1`, and S11 for every exhaustion sequence** (`R_one2`, `one2_mem_domain`, `semigroup_one2`, `conservative_of_esa`), for a bare `DiffusionTriple` with `ESAProp` (= F10); needs neither CD nor S11. |
| `Poincare` | `CD(ρ,∞)`, `ρ>0`, probability ⇒ `T.PI (1/ρ)` (`poincare_of_CD_infty`); `CD(ρ,n)`, `n>1` ⇒ `T.PI ((1-n⁻¹)/ρ)` (Lichnerowicz, gap `ρn/(n-1)`; `poincare_of_CD_dim`); extension to `𝒟(ℰ)` (`poincare_extend_domain`); Hilbert forms `hasSpectralGap_of_PI`, `expDecay_of_PI`, `hasSpectralGap_of_CD_dim`. Route: integrated squared inequality + `Hilbert.gap_of_square` + S10. |
| `ALevel`, `GammaCalculus` | `L`, `Γ(u,u)` depend only on a.e.-classes on `𝒜`; `Γ(ψ∘g,h) = ψ'(g)Γ(g,h)`, `Γ(ψ∘g)=ψ'(g)²Γ(g)`, `Γ(ε+g)=Γ(g)`, `Γ(f²)=4f²Γ(f)` on `𝒜`; representatives `Pt` in `𝒜` of `P_t[f]` (F8) with positivity. |
| `Convergence` | `∫Θ(ε+P_sφ) → Θ(ε+∫φ)` (`Θ = r log r`) as `s→∞`, from the spectral gap. |

## Conditional (explicit hypothesis structures, never axioms)

### G1.  `FullTriple.GradientInterpolation T`  (Cor. 3.3.19 / proof of Thm 3.3.18, `GradientBound.lean`)
Proved from it (`gradient_integrated`, `gradient_bound`): for `f ∈ 𝒜₀`, `t ≥ 0`,
`Γ(P_t f) ≤ e^{-2ρt} P_t(Γ f)` a.e., under `CD(ρ,n)` (any `n`).  Everything but the differentiation of
`Φ(s) = ∫ P_s h · Γ(P_{t-s} f)` is proved (Gronwall step, end points `P_0 = id`, symmetry of `P_t`,
a.e.-congruence of `Γ`, F2 to pass from `∫ h(·) ≥ 0` for all `h ≥ 0 ∈ 𝒜₀` to a.e. `≥ 0`).
**Missing lemma (exact):** for `f,h ∈ 𝒜₀`, `h ≥ 0`, `t ≥ 0`, `k_s = P_s h`, `g_s = P_{t-s} f` (reps in `𝒜`):
`s ↦ ∫ k_s Γ(g_s)` is continuous on `[0,t]`, and on `(0,t)` the integrands `k_s Γ(g_s)`, `k_s Γ₂(g_s)`
are integrable and `Φ' = 2∫ k_s Γ₂(g_s)`.  The book obtains this from Lemmas 3.3.20–3.3.21 using
`√(Γ(P_t f)+ε²) - ε ∈ 𝒟(ℰ)`, i.e. needs: (a) extension of `Γ₂` and of the Hessian to `𝒟(L)`
(Prop. 3.3.16 (i),(iii)–(viii)); (b) identification of `Γ_𝒜(f)` with the closed form for
`f ∈ 𝒜 ∩ L²` with `Γ(f) ∈ L¹` (Props. 3.3.5–3.3.6; `Γ` is not extended to `𝒟(ℰ)` in the surface);
(c) symmetric integration by parts `∫ Lk·G = ∫ k·LG` for `k = P_s h ∈ 𝒜∖𝒜₀`, `G ∈ 𝒟(ℰ) ∩ 𝒜`
(Prop. 3.3.17 / (3.3.5)).  For a *compact* triple (`𝒜=𝒜₀`) it should be provable by differentiating in
the graph norm of `L`; not done.
**Strong (√) form, Thm 3.3.18: DONE (round 12), see the section "Round 12" below** (`Theory/Strong/*`): the pointwise
inequality (3.3.6) `Γ(Γ f) ≤ 4(Γ₂(f)-ρΓ(f))Γ(f)` is PROVED on `𝒜` for every full triple with `CD(ρ,n)`
(`FullTriple.reinforced_cd`), and `√Γ(P_t f) ≤ e^{-ρt} P_t(√Γ f)` is proved for `ρ ≥ 0` from the explicit analytic
structure `StrongInterpolation` (discharged for compact triples, OU), and for Lebesgue by the heat kernel.

### G3.  `FullTriple.EntropyInterpolation T`  (de Bruijn + `Φ''`; Prop. 5.7.1, §5.5, `LogSobolev.lean`)
Proved from it (`ent_le_fisher`, `ent_sq_add_le`, `logSobolev_of_CD_infty`, `logSobolev_extend_domain`):
`CD(ρ,n)`, `ρ>0`, probability ⇒ `T.LS (1/ρ) 0` (`Ent(f²) ≤ (2/ρ)ℰ(f)`) on `𝒜₀` and on `𝒟(ℰ)`.
Proved there: `g_s = ε+P_sφ ∈ [ε,ε+M]`, `Γ(log g)·g = Γ(g)/g` (F6 with a smooth cutoff of `log`),
`CD` applied to `log g_s ∈ 𝒜` ⇒ Fisher decay `I(s) ≤ e^{-2ρs}I(0)` (via `BE.fisher_decay`), entropy–Fisher
inequality, the `f²` and `ε → 0` steps, limit at `∞` (from the gap).
**Missing lemma (exact), for `φ∈𝒜₀`, `0≤φ≤M`, `ε>0`:** with `e(s)=∫g_s log g_s`, `I(s)=∫Γ(g_s)/g_s`,
`J(s)=∫ g_s Γ₂(Λ∘g_s)` (`Λ` a smooth cutoff of `log` on `[ε,ε+M]`): `e`, `I` continuous on `[0,∞)`;
`e' = -I` on `(0,∞)`; `g_sΓ₂(Λ∘g_s)`, `g_sΓ(Λ∘g_s)` integrable and `I' = -2J`.  Same analytic content as G1
(regularity of `s ↦ P_s φ` in `𝒟(L)`, symmetric ibp on `𝒜`), plus differentiation under `∫` with
`Θ`-compositions.

## Not done / documented only

* **G4.  Mass conservation, infinite `μ` (Thm 3.3.23): DONE modulo the gradient bound (round 11).**  Finite `μ`: ESA alone
  (`ESAOne`).  Infinite `μ`: `Theory/Conservation/{Hilbert,ExtAlgebra,Estimate,Mass,Finite,Compact}.lean`.
  Completeness is `DiffusionTriple.IsComplete` (`Frozen/Complete.lean`).  Proved (no sorry, standard axioms):
  `ExtendedAlgebra.conservative_of_complete` (complete + weak gradient bound ⇒ S11 for every exhaustion sequence),
  `ExtendedAlgebra.isFiniteMeasure_of_complete` (`ρ>0` + S10 + complete + gradient bound ⇒ `μ` finite),
  and the `FullTriple`/`CompactTriple` forms.  They are stated over `ExtendedAlgebra D A` (S11 is a field of `FullTriple`, so
  the theorem would be vacuous there).  **Remaining exact gap:** the hypothesis `HasGradientBound D A ρ`
  (`Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)`, Cor. 3.3.19) is available only for compact triples and for full triples satisfying
  `GradientInterpolation` (G1, still open for non-compact triples); the book's use of it is exactly this weak form
  (the strong form 3.3.18 is not needed).  **Round 12:** Lebesgue and OU are PROVED complete (real cutoffs, `Theory/Complete/`),
  and the theorem has genuine non-compact applications: `ouFull_conservative_of_complete`,
  `lebesgue_conservative_of_complete` (infinite measure; weak gradient bound from the heat kernel,
  `lebesgue_hasGradientBound`).  The book's `√Γ ξ ∈ L¹` step is replaced by `2|η|√Γη ≤ η²+Γη`, ξ=η².
* **G5.  Props. 3.3.16 (i),(iii)–(viii) and 3.3.17 as operator statements.**  PARTIALLY DONE (round 12,
  `Theory/Extension/*`): `FullTriple.gamma_limits` = Prop 3.3.16 (i), (ii), (iii) for `Γ` and `Γ₂` (extension to `𝒟(L)` as
  `L¹`-limit along any graph-convergent sequence of test functions, independence of the sequence, `∫Γ₂(u) = ‖Lu‖²`,
  `∫Γ(u) = −⟪Lu,u⟫`, extended `CD(ρ,n)`).  **Still open (exact):** the Hessian `H(f)(g,h)` and (iv)–(viii)
  (extension to `𝒟(L) × 𝒟(ℰ) × 𝒜₀`, product rule (vi)–(vii), inequality (3.3.7) extended (viii)); Prop 3.3.17
  (identification of the `𝒟(L)`-definition of `Γ₂`/`H` with the `𝒜`-definition on `𝒜 ∩ 𝒟(L)` and the converse under ergodicity;
  it needs the identification of `Γ` on `𝒜 ∩ 𝒟(ℰ)` with the closed-form extension, Props 3.3.5–3.3.6, also not in the surface).
  Note Remark 3.3.15 (CD from `𝒜₀` to `𝒜`) is not needed: the frozen `FullTriple.CD` is already stated on all of `𝒜`.
* `FullTriple.CD` for the finite-dimensional LSI constant `ρn/(n-1)` (Thm 5.7.4 with `n<∞`, via the integrated
  chain rule (5.7.6)–(5.7.12) for `e^{ag}`): not done (only `n`-independent constant `1/ρ`, from `CD(ρ,n) ⇒ CD(ρ,∞)`).

## Update: compact triples (`Theory/Compact/`)

`compact_gradientInterpolation` and `compact_entropyInterpolation` prove G1 and G3 as theorems for every
`CompactTriple` (`𝒜 = 𝒜₀`); the gradient bound, Fisher decay and (for `ρ>0`) the log-Sobolev inequality are therefore
unconditional there, and the circle has `Γ(P_t f) ≤ P_t Γ f`, `e' = -I`, `I' ≤ 0`.  See `Compact/GAPS_COMPACT.md`.
G1/G3 remain open (hypotheses) for non-compact full triples.

## Round 12: strong gradient bound, completeness, non-compact applications, Γ₂ extension

| Statement | Lean | Status |
|---|---|---|
| Hessian product rule (3.3.4) `Γ₂(hk,g) = hΓ₂(k,g)+kΓ₂(h,g)+Γ(h,Γ(k,g))+Γ(k,Γ(h,g))−Γ(g,Γ(h,k))` | `FullTriple.Γ₂_mul_left` (`Strong/Calculus`) | proved (F6, `k=2`) |
| Reinforced CD (3.3.6) `Γ(Γf) ≤ 4(Γ₂(f)−ρΓ(f))Γ(f)`, and `Γ(w,Γf)² ≤ 2K(f)(Γ(f)Γ(w)+Γ(f,w)²)` | `FullTriple.reinforced_cd`, `hessian_ineq` (`Strong/Reinforced`) | proved for every `FullTriple` with `CD(ρ,n)`, any `ρ ∈ ℝ` |
| Lemma 3.3.21 pointwise step, Gronwall, `ε→0` | `FullTriple.strongD_ge`, `strong_integrated`, `strong_eps`, `strong_of_eps` | proved (`ρ ≥ 0`) |
| **Thm 3.3.18** `√Γ(P_t f) ≤ e^{-ρt}P_t(√Γ f)` | `FullTriple.strong_gradient_bound` | conditional on `StrongInterpolation` (analytic differentiation of `Φ_ε(s)=∫P_sh ψ_ε(Γ P_{t-s}f)`), `ρ ≥ 0` |
| `StrongInterpolation` for compact triples | `CompactTriple.strongInterpolation` (via `hasDerivAt_ucls`: `L²`-differentiability of `s↦[Γ(P_{t-s}f)]` by the energy estimate `‖Γ(a,b)‖₂² ≤ ‖Γb‖_∞ ℰ(a)`, `ℰ(a) ≤ ‖a‖‖La‖`) | proved; `compact_strong_gradient_bound`, `circle_/ouBCompact_/sphere_strong_gradient_bound` |
| `StrongInterpolation` for OU | `ouFull_StrongInterpolation`, `ouFull_strong_gradient_bound` (`ρ = 1`) | proved (Mehler calculus + two Gaussian IBPs) |
| Strong bound for Lebesgue (`ρ = 0`, infinite μ) | `Lebesgue.lebesgue_strong_gradient_bound` | proved by the heat kernel + Jensen (`StrongInterpolation` is not used) |
| Completeness (Def 3.3.9): Lebesgue, OU | `lebesgueDiffusion_isComplete`, `ouDiff_isComplete` (`Complete/Real`: real cutoffs `χ(x/(M(k+1)))`) | proved |
| Non-compact applications of Thm 3.3.23 (1st claim) | `ouFull_conservative_of_complete`, `lebesgue_conservative_of_complete`, `lebesgue_hasGradientBound` | proved |
| Prop 3.3.16 (i)–(iii) for `Γ`, `Γ₂` | `FullTriple.gamma_limits` (`Extension/Main`) | proved (see G5 for what is missing) |

**Not done (exact gaps):**
* `StrongInterpolation` / `GradientInterpolation` / `EntropyInterpolation` for a *general non-compact* `FullTriple`
  (they remain hypotheses; discharged only for compact triples and OU, plus `HasGradientBound` and the strong bound for
  Lebesgue by kernels).  The obstruction is the one of G1: differentiation of `s ↦ ∫ P_s h · Θ(Γ(P_{t-s}f))` needs
  `L²`/`L¹`-regularity of the orbit in `𝒟(L)` *and* control of `Γ(P_s f)` in `L^∞` that the abstract `𝒜`, F1–F10 do not provide
  (for compact triples `𝒜 = 𝒜₀` gives it via `Γ(P_τ f) ≤ ‖Γ f‖_∞`).  A generic discharge would need the extended `Γ₂`/Hessian of
  Props 3.3.16–3.3.17 (above) to run the book's route (Lemmas 3.3.20–3.3.21 with `ε`-regularised `√`).
* Thm 3.3.18 for `ρ < 0`: the `ε`-form needs the error term `ρ ε ∫ P_s h` (uses `∫P_s h ≤ ∫h`); not done (all instances have `ρ ≥ 0`).
* Lebesgue `GradientInterpolation`/`EntropyInterpolation` as structures (the entropy one is moot: `ρ = 0` gives no LSI; the
  gradient one is subsumed by `lebesgue_hasGradientBound`, which is exactly the hypothesis of Thm 3.3.23).
