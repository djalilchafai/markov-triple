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
  **Round 14 update (`Theory/Extension/{Closed*,Hess*,Ident*,Gamma2Ident}.lean`, `Extension/STATEMENTS_R14.md`, `BGL/AUDIT_R14_SELF.md`):**
  DONE (no `sorry`, standard axioms): `Γ` on `𝒟(ℰ)` (`gammaE`) with Leibniz rule; Props 3.3.5 (i)–(iii), 3.3.6 (i)–(ii); the
  Hessian on `𝒜`, (3.3.4), (3.3.7) for all `f,g,h ∈ 𝒜` (`hessian_general_ineq`), (3.3.5) IBP; Prop 3.3.16 (iv), (v) (`L¹` form),
  (vi), (viii) (`hessE`, `hessE_tendsto`, `hessE_mulE`, `hessE_ineq`); Prop 3.3.17: identification of `H` (`hessE_eq_Hess`,
  `hessE_eq_Hess'`) and of `Γ₂` (`Γ₂_ext_eq`), `Γ(f), Γ₂(f) ∈ L¹`, `∫Γ₂(f) = ∫(Lf)²` (`integrable_Γ₂_of_domain`), and the symmetric
  IBP `ibp_of_domain` (input (c) for Lemmas 3.3.20–3.3.21).  3.3.16 (vii) (`gamma2E`, `mulE_mem_domain`, `gamma2E_mulE`) and the `L²` form of (v) (`hess2_exists`) are also done (round 14b).
  **Still open:** only the converse of 3.3.17 under ergodicity (spectral argument).
  **Round 15 (`Extension/Converse.lean`):** the converse of 3.3.17 is proved CONDITIONALLY on the named Prop `FullTriple.Core2` (`𝒜₀` core for `L²`, implicit in the book, ERRATA R15-1); unconditional converse OPEN.
  **Round 15 update (gap closure after the independent audit; `Extension/{SeqLin,HessExtLin,Gamma2ELin,GammaELin}.lean`, `STATEMENTS_R15_Gaps.md`, `BGL/AUDIT_R15_GAPS_SELF.md`, ERRATA E5):** added bilinearity/boundedness/identification of `hessE` (3.3.16 (iv)), the general 2nd/3rd statements of (v), bilinearity/symmetry/bound of `gamma2E` and `gammaE`, `gammaE` Cauchy–Schwarz, and the link `GG2 a a = G2cls a` with `Γ₂_ext_eq_gamma2E`.  Still open: converse of 3.3.17 only.
  Note Remark 3.3.15 (CD from `𝒜₀` to `𝒜`) is not needed: the frozen `FullTriple.CD` is already stated on all of `𝒜`.
* **Finite-dimensional LSI constant `(n-1)/(ρ n)` (Thm 5.7.4, `1 < n < ∞`): DONE (round 14), conditional on a named structure.**
  `Theory/LogSobolevDimChain.lean`: (5.7.6) `Γ₂_exp`, (5.7.7)-(5.7.12) `integral_exp_L_Γ`, `integral_exp_sq_L`,
  `integral_exp_Γ₂_ge`, `integral_exp_Γ₂_ge'` (for `g ∈ 𝒜₀` **under the extra hypothesis `e^{g/2} ∈ 𝒜₀`**, which the book obtains from Prop. 3.3.17 without stating it; discharged on compact triples).  `Theory/LogSobolevDim.lean`:
  `FullTriple.logSobolev_of_CD_dim` (conditional on `EntropyInterpolation` and `FiniteDimInterpolation`), and unconditional
  `CompactTriple.compact_logSobolev_dim`; `Instances/Sphere/LogSobolevDim.lean`: `sphere_LS_dim : LS(1/3, 0)` on the zonal `S³`.
  **Exact missing input for non-compact triples** (`FiniteDimInterpolation`): book p. 270 (boundedness of `Γ(P_t f)`, `L P_t f`) and
  p. 272 (extension of (5.7.12) from `e^g`, `g ∈ 𝒜₀` to `f ∈ 𝒜` bounded with `Γ(f)`, `Lf`, "by Prop. 3.3.6 and Lemma 3.3.16");
  the extension needs the operator-level Props 3.3.16 (iv)-(viii)/3.3.17 (G5).  Not done: `n = 1` (torus, p. 272), optimality.

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
| **Thm 3.3.18** `√Γ(P_t f) ≤ e^{-ρt}P_t(√Γ f)` | `FullTriple.strong_gradient_bound` | now UNCONDITIONAL via `FullTriple.strongInterpolation` (round 15, `Theory/Interp`; was conditional on `StrongInterpolation`) (analytic differentiation of `Φ_ε(s)=∫P_sh ψ_ε(Γ P_{t-s}f)`), `ρ ≥ 0` |
| `StrongInterpolation` for compact triples | `CompactTriple.strongInterpolation` (via `hasDerivAt_ucls`: `L²`-differentiability of `s↦[Γ(P_{t-s}f)]` by the energy estimate `‖Γ(a,b)‖₂² ≤ ‖Γb‖_∞ ℰ(a)`, `ℰ(a) ≤ ‖a‖‖La‖`) | proved; `compact_strong_gradient_bound`, `circle_/ouBCompact_/sphere_strong_gradient_bound` |
| `StrongInterpolation` for OU | `ouFull_StrongInterpolation`, `ouFull_strong_gradient_bound` (`ρ = 1`) | proved (Mehler calculus + two Gaussian IBPs) |
| Strong bound for Lebesgue (`ρ = 0`, infinite μ) | `Lebesgue.lebesgue_strong_gradient_bound` | proved by the heat kernel + Jensen (`StrongInterpolation` is not used) |
| Completeness (Def 3.3.9): Lebesgue, OU | `lebesgueDiffusion_isComplete`, `ouDiff_isComplete` (`Complete/Real`: real cutoffs `χ(x/(M(k+1)))`) | proved |
| Non-compact applications of Thm 3.3.23 (1st claim) | `ouFull_conservative_of_complete`, `lebesgue_conservative_of_complete`, `lebesgue_hasGradientBound` | proved |
| Prop 3.3.16 (i)–(iii) for `Γ`, `Γ₂` | `FullTriple.gamma_limits` (`Extension/Main`) | proved (see G5 for what is missing) |

**Not done (exact gaps):**
* **Update (round 15, `Theory/Interp`):** `StrongInterpolation` IS now discharged for every `FullTriple` (`FullTriple.strongInterpolation`, Lemmas 3.3.20–3.3.21).  The text below is the earlier state; what remains open is `GradientInterpolation` (not a book statement), `EntropyInterpolation` and `FiniteDimInterpolation` (and the weak Cor. 3.3.19 via Jensen).
* `StrongInterpolation` / `GradientInterpolation` / `EntropyInterpolation` for a *general non-compact* `FullTriple`
  (they remained hypotheses at the time of writing; discharged only for compact triples and OU, plus `HasGradientBound` and the strong bound for
  Lebesgue by kernels).  The obstruction is the one of G1: differentiation of `s ↦ ∫ P_s h · Θ(Γ(P_{t-s}f))` needs
  `L²`/`L¹`-regularity of the orbit in `𝒟(L)` *and* control of `Γ(P_s f)` in `L^∞` that the abstract `𝒜`, F1–F10 do not provide
  (for compact triples `𝒜 = 𝒜₀` gives it via `Γ(P_τ f) ≤ ‖Γ f‖_∞`).  A generic discharge would need the extended `Γ₂`/Hessian of
  Props 3.3.16–3.3.17 (above) to run the book's route (Lemmas 3.3.20–3.3.21 with `ε`-regularised `√`).
* Thm 3.3.18 for `ρ < 0`: the `ε`-form needs the error term `ρ ε ∫ P_s h` (uses `∫P_s h ≤ ∫h`); not done (all instances have `ρ ≥ 0`).
* Lebesgue `GradientInterpolation`/`EntropyInterpolation` as structures (the entropy one is moot: `ρ = 0` gives no LSI; the
  gradient one is subsumed by `lebesgue_hasGradientBound`, which is exactly the hypothesis of Thm 3.3.23).

## Gibbs `e^{-V}dx`, `V'' ≥ ρ > 0` (files `Instances/Gibbs/Funct*.lean`; book route only)

Audit (book statements, BGL ch. 3): Thm 3.3.18 / Cor 3.3.19 use a Diffusion Triple + ESA (F10) + extended algebra
`𝒜` (F1–F8, in particular F8: `P_t 𝒜₀ ⊂ 𝒜`) + CD(ρ,∞); they do not use S10/S11/F9.  ESA for Gibbs: Cor 3.2.2 /
Prop 3.3.11 (completeness + connexity + weak hypo-ellipticity, Def 3.3.8).  Ergodicity S10: Prop 3.3.10.
S11: finite μ + ESA (`conservative_of_esa`); Thm 3.3.23 is not needed.  Poincaré: only integrated Γ₂, ESA, S10.

Proved (standard axioms only), general (any Diffusion Triple, abstract `𝒜`): `PreFull` (the semigroup-free F1, F2, F4–F7, F9),
`PreFull.cutoff_estimate`/`gradient_eq_zero` (the cut-off computation of Prop 3.2.1), `DiffusionTriple.ESAProp_of_weakHypo`
(Prop 3.3.11), `DiffusionTriple.ergodic_of_weakHypo` (Prop 3.3.10).  **Deviation, Prop 3.3.10:** the book writes
`0 = ∫ f Lf = -∫ Γ(f)` for `f ∈ 𝒟(L) ∩ 𝒜`, an integration by parts beyond F7 (`g ∈ 𝒜₀`); the library instead gets
`Γ(f) = 0` from the Prop 3.2.1 cut-off computation (needs completeness).  Gibbs: `ibp_sm` (F7 on `C^∞`), `gibbs_preFull`,
`gibbsDiff_esaProp`, `gibbsDiff_ergodic` (both need `WeakHypo`, Def 3.3.8), `gibbs_integral_Γ₂` (3.3.8),
`gibbs_integrated_CD`, **`gibbs_poincare`** (`PI(1/ρ)`), `gibbs_spectralGap`, `gibbs_expDecay` (all under `WeakHypo` only,
no F8, no gradient bound), and `gibbsFull : FullTriple ℝ` (under `WeakHypo` and `GibbsData.F8`) with `gibbsFull_CD`,
`gibbs_CD_pointwise`, `gibbsFull_poincare`.
`gibbsFull_logSobolev`, `gibbsFull_gradient_bound` are conditional on `EntropyInterpolation` / `GradientInterpolation`.
**ROUND 15 UPDATE: (a) and (b) below are now PROVED for every `GibbsData` (`GibbsData.weakHypo`, `GibbsData.f8`; files `Instances/Gibbs/Reg*.lean`, statements in `STATEMENTS_R15_Reg.md`); unconditional corollaries `gibbsFull_unconditional`, `gibbsFull_CD_unconditional`, `gibbs_poincare_unconditional`, etc. in `RegMain.lean`. Only (c) remains open.**
**Exact missing inputs (historical, before round 15):** (a) weak hypo-ellipticity (`GibbsData.WeakHypo`: elliptic regularity of `f'' - V' f' = λ f`, λ = 0, 1 used; the book
cites Sect. 1.12 without proof); (b) F8 (smoothness of the Friedrichs semigroup, Def 3.3.1 (viii), also unproved in the
book: "very often true"); (c) the non-compact discharge of `GradientInterpolation`/`EntropyInterpolation`
(Lemmas 3.3.20–3.3.21 with Props 3.3.16 (iv)–(viii), 3.3.17), the open generic gap above.

## Round 15 (Core2): converse of Prop 3.3.17

`FullTriple.mem_domain_of_Γ₂` (converse, p. 162) is conditional on `FullTriple.Core2` (ERRATA R15-1).  Status (`Extension/STATEMENTS_R15_Core2.md`,
`BGL/AUDIT_R15_CORE2_SELF.md`): `core2_of_dense` reduces `Core2` to density of `(1−L)²𝒜₀` in `L²`; **unconditional converse** for
compact triples (`CompactTriple.mem_domain_of_A`, trivial), OU (`ou_mem_domain_of_Γ₂`) and the Brownian triple (`lebesgue_mem_domain_of_Γ₂`).
**Open (exact):** `Core2` for a general `FullTriple`.  **Round 17 (Stream A, `Instances/Gibbs/Core2*.lean`, `STATEMENTS_R17_Core2.md`, `BGL/AUDIT_R17_GIBBSCORE2.md`):**
`Core2` and hence the UNCONDITIONAL converse of 3.3.17 are PROVED for 1-D Gibbs triples with bounded `V', V'', V'''` (`GibbsData.gibbsFull_core2`,
`GibbsData.gibbs_mem_domain_of_Γ₂`; non-vacuous: `V = √(1+x²)`, `sqrtGibbs_bddJet`).  **Round 18 (Stream A2, `Instances/Gibbs/Core2W*.lean`, `STATEMENTS_R18_Core2.md`, `BGL/AUDIT_R18_CORE2.md`):** the cut-off Bochner/Hardy estimates
`memLp_of_BE`, `memLp_of_hardy` give `Core2` and the UNCONDITIONAL converse of 3.3.17 for 1-D Gibbs with `|V''|,|V'''| ≤ C(1+|V'|)` (`GrowHess`; `V'` arbitrary, any `ρ`,
including uniformly convex non-Gaussian: `GibbsData.gibbsFull_core2_of_growHess`, `gibbs_mem_domain_of_Γ₂_growHess`; witnesses `cosGibbs`, `quarGibbs`).
**Still open (exact):** `Core2` for 1-D Gibbs outside `GrowHess` (e.g. `V''/|V'|` unbounded, as `e^{x²}`-type), for arbitrary smooth `V`
(equivalent to e.s.a. of `L²` on `C_c^∞`, possibly false), and for `EllData`/`GibbsRdData` on `ℝ^d` (needs `∇²v ∈ L²(μ)` by a cut-off Bochner estimate and the
`d`-dimensional commutators of `L²` with cut-offs).

## Round 15 "Interp": the non-compact discharge of `StrongInterpolation` (files `Theory/Interp/*`, `Instances/Gibbs/InterpMain`, `Instances/OU/InterpGeneric`)
Statements: `Theory/Interp/STATEMENTS_R15_Interp.md`; self-audit: `BGL/AUDIT_R15_INTERP_SELF.md`.
* **G1' DISCHARGED for every `FullTriple`**: `FullTriple.strongInterpolation : T.CD ρ n → T.StrongInterpolation` (any `ρ`, `n`; no compactness, no converse of 3.3.17),
  hence `FullTriple.strong_gradient_bound_unconditional` (Thm 3.3.18, `ρ ≥ 0`), `gibbsFull_strong_gradient_bound_unconditional` (`V'' ≥ ρ ≥ 0`),
  `ouFull_strongInterpolation_generic`.  Route = book's Lemmas 3.3.20–3.3.21 with the "justified" differentiation made explicit (`L¹`/`L²` calculus).
* **G1 (`GradientInterpolation`, `Φ' = 2∫P_sh Γ₂`)**: NOT a statement of the book (the book never differentiates `∫P_sh Γ(P_{t-s}f)`: `Γ(P_{t-s}f) ∈ L¹` only, not in `𝒟(ℰ)`);
  it stays a hypothesis for non-compact triples.  The weak gradient bound (Cor. 3.3.19) for `ρ ≥ 0` would follow from `strong_gradient_bound_unconditional` + Jensen
  `(P_t w)² ≤ P_t(w²)` (sub-Markov `P_t`): (superseded in round 16: the Jensen lemma `jensen_sq` and the weak bound `hasGradientBound_unconditional` ARE now in the library, `Theory/Interp/Jensen*.lean`).
* **G3, G3'**: not attempted in this stage (superseded in round 16: G3 `EntropyInterpolation` is discharged by `FullTriple.entropyInterpolation` for finite-measure full triples with ρ ≥ 0, G3' `bdd` by `finiteDim_bdd`; only `ext` remains; earlier note: see `AUDIT_R15_INTERP_SELF.md` §4 for the exact missing analytic content: `L¹`-differentiation of `I(s) = ∫Γ(g_s)/g_s` and `I' = -2J`).

## Round 16 "Jensen": weak gradient bound for every FullTriple (`Theory/Interp/Jensen*.lean`, `Instances/Gibbs/JensenMain.lean`)
Statements `Theory/Interp/STATEMENTS_R16_Jensen.md`; self-audit `BGL/AUDIT_R16_JENSEN_SELF.md`.
* `jensen_sq` (generic positive sub-Markov `L^2` operator): `(P w)^2 <= P(w^2)`.  **`FullTriple.gradient_bound_unconditional` (Cor 3.3.19, `rho >= 0`) PROVED for every FullTriple with `CD(rho,n)`;**
  `hasGradientBound_unconditional`, `conservative_of_complete_unconditional` (Thm 3.3.23 for complete triples, no `GradientInterpolation`), Gibbs (R and R^d) corollaries.
* Still open: `rho < 0` (strong form needs the eps error term); G1 `GradientInterpolation` (not a book statement); G3, G3'.

## Round 16 "Entropy": G3 discharged; G3' reduced to `ext` (files `Theory/Interp/Entropy*.lean`)
Statements: `Theory/Interp/STATEMENTS_R16_Entropy.md`; audit: `BGL/AUDIT_R16_ENTROPY_SELF.md`; errata R16-E1..E3.
* **G3 DISCHARGED**: `FullTriple.entropyInterpolation : T.CD ρ n → 0 ≤ ρ → [IsFiniteMeasure T.μ] → T.EntropyInterpolation` for every (non-compact) `FullTriple`.
  Hence **unconditional LSI** `FullTriple.logSobolev_unconditional` (`LS(1/ρ,0)`, probability measure, `CD(ρ,n)`, `ρ>0`), `logSobolev_domain_unconditional`,
  `GibbsData.gibbsFull_logSobolev_unconditional` (`V'' ≥ ρ > 0`).  Finite `μ` is necessary (otherwise `entE` is junk), `ρ ≥ 0` used for `Γ(P_tφ)` bounded.
* **G3' (`FiniteDimInterpolation κ`)**: field `bdd` PROVED (`finiteDim_bdd`).  Field `ext` (BGL p. 272) (superseded in round 16, R16-X1: now PROVED for finite-measure full triples, `Theory/Interp/Ext*.lean`); `finiteDimInterpolation_of_ext`, `logSobolev_dim_of_ext`
  reduce Thm 5.7.4 for non-compact triples to that single statement.  Exact remainder: AUDIT_R16_ENTROPY_SELF.md §4.

## Round 16 "Ext": G3' discharged (files `Theory/Interp/Ext*.lean`)
Statements `Theory/Interp/STATEMENTS_R16_Ext.md`; audit `BGL/AUDIT_R16_EXT_SELF.md`; errata R16-X1, X2.
* **`FiniteDimInterpolation` field `ext` PROVED** (`FullTriple.finiteDimExt`): bounded `f in A` -> `[f] in D(L)` (Prop 3.3.6), `Gamma_2` integrable and
  `int Gamma_2 = int (Lf)^2` (Prop 3.3.17), (5.7.7)-(5.7.12) redone for bounded `g in A` (`ibp_of_domain`; `Gamma(Gamma g) in L^1` by (3.3.6)).
  Hence `FullTriple.finiteDimInterpolation_of_CD` and **unconditional Thm 5.7.4 for every FullTriple of finite measure**: `FullTriple.logSobolev_dim_unconditional`.
* Still open: `rho < 0`, infinite `mu`, `n = 1`.

**Scope note (audit R16-Ext).** `logSobolev_dim_unconditional` / `finiteDimInterpolation_of_CD` are unconditional for every finite-measure `FullTriple` with `CD ρ n`, `1 < n < ∞`, `ρ ≥ 0`, but every known witness of finite-n curvature in the library is on a COMPACT triple (`sphere_CD_two_three`); the non-compact instances (OU, Lebesgue, Gibbs) have `n = ∞` or infinite measure, so the new theorems have no non-compact application yet and their non-compact content is not exercised.

## Round 16: elliptic regularity chain and `EllReg` (audit R16-Glue)
`EllData.EllReg` is PROVED for every `EllData d` (`GibbsRd/EllRegProof.lean`: MemLp ⇒ LocL2, Friedrichs L²_loc ⇒ H¹_loc, E3 `interior_sobolev`, Sobolev embedding of order m+d), hence `weakHypo_unconditional` and `f8_unconditional`, and the unconditional corollaries for Gibbs on ℝ^d and the weighted Riemannian chart (`GibbsRd/Unconditional.lean`, `Riemannian/Unconditional.lean`). The earlier remarks in this file and in `GibbsRd/*`, `Riemannian/*` that `WeakHypo`/`F8` are named hypotheses for d ≥ 1 are superseded (they remain correct as statements about those conditional theorems).  Still open: the Sobolev embedding is not sharp (order m+d instead of m+⌊d/2⌋+1); `Curv ρ` / `HessGe` remain hypotheses; the Riemannian chart is a single global chart with bounded co-metric.

## Round 17: stochastic layer (see `MarkovTriple/Stochastic/AUDIT_R17.md`)
PROVED: joint measurability in `(t,x)` of the Feller kernels, so `fellerMarkovProcessBridge` (every conservative Feller triple on a compact metrizable space with full-support finite `μ`) and `Sphere.sphereMarkovProcessBridge`; exact Chapman-Kolmogorov for the Riesz kernels on a conull properly exceptional set for any COUNTABLE set of times (`exists_exact_ck`, `rieszKernel_exists_exact_ck`).
OPEN: (1) exact CK for ALL real times without the Feller property (and hence `KernelBridge`/`MarkovProcessBridge` for plain Riesz kernels); (2) non-compact (locally compact σ-compact) Riesz-Markov-Feller extension (work list in AUDIT_R17 item 3); (3) Feller is a hypothesis, not automatic.
`EllData.EllReg` is PROVED for every `EllData d` (`GibbsRd/EllRegProof.lean`: MemLp ⇒ LocL2, Friedrichs L²_loc ⇒ H¹_loc, E3 `interior_sobolev`, Sobolev embedding of order m+d), hence `weakHypo_unconditional` and `f8_unconditional`, and the unconditional corollaries for Gibbs on ℝ^d and the weighted Riemannian chart (`GibbsRd/Unconditional.lean`, `Riemannian/Unconditional.lean`). The earlier remarks in this file and in `GibbsRd/*`, `Riemannian/*` that `WeakHypo`/`F8` are named hypotheses for d ≥ 1 are superseded (they remain correct as statements about those conditional theorems).  **Round 17 (SobSharp):** the Sobolev-embedding item is CLOSED: `Sob.sob_contDiff_rep_sharp` (`HasSobL2 k f`, `d + 2m < 2k`, i.e. `k > m + d/2`, ⇒ `C^m` representative; Fourier/Plancherel route, Mathlib Schwartz Plancherel) with `sob_contDiff_rep_sharp'` (`k = m+⌊d/2⌋+1`), `sob_continuous_rep_sharp`, `smooth_of_weak_all_orders_sharp`, and `EllData.ellReg_sharp`/`ellReg_sharp_order`/`ellReg_of_sharp` (chain length `m+⌊d/2⌋+1`); `ellReg`/`sob_contDiff_rep_L2` (order `m+d`) are kept unchanged (`AUDIT_R17_SOBSHARP.md`; not done: optimality of the threshold, `L^p`, `p≠2`). Still open (R16 list, minus the Sobolev item): `Curv ρ` / `HessGe` remain hypotheses; the Riemannian chart is a single global chart with bounded co-metric.
## Round 17 "Noncompact": finite-`n` CD on the zonal `S³` minus its poles: COSMETIC non-compact instance (files `Instances/SphereOpen/*`; ERRATA R17-M2/M3)
Statements `Instances/SphereOpen/STATEMENTS_R17_Noncompact.md`; audit `BGL/AUDIT_R17_NONCOMPACT.md`; errata R17-1..4.
* **PROVED**: `SphereOpen.oFull : FullTriple ZonO` on the non-compact `ZonO = (-1,1)` (finite probability measure `μO`), F1-F10, S10, S11 all theorems;
  `oFull_CD : CD 2 3`, `oFull_finiteDimInterpolation`, `oFull_LS : LS (1/3) 0` (Thm 5.7.4, `C=(n-1)/(ρn)`), `oFull_Γ_ne_zero`, `oFull_μ_pos_of_open`.
  Axioms: `propext`, `Classical.choice`, `Quot.sound` only.  This does NOT close the Round 16 "Ext" gap: the non-compact content is not exercised (`FullTriple` has no topology, `A = A₀`, so `ext` is vacuous).
* **Caveat (read before citing)**: the instance is the zonal `S³` triple restricted to a dense conull open subset (`L²`, `R`, `P_t` transported unitarily;
  `A = A₀`); non-compactness is topological only.  Nothing about essential self-adjointness of `C_c^∞(-1,1)` (true only for Gegenbauer dimension `n ≥ 4`)
  or boundary regularity is proved.  Not built: other `n`, other Jacobi parameters, `C_c^∞` as test algebra.
* **Obstruction (math remark, not formalized)**: `ρ>0`, `n<∞` ⇒ bounded intrinsic diameter (Bonnet-Myers), so no proper `d_Γ`-complete state space (the `EllData`/`RiemData`/`GibbsRdData` charts) can carry such a triple; Laguerre, OU, Student-type have `ρ ≤ 0` or `n = ∞`.  CORRECTION (R17-M3): Jacobi/Gegenbauer are NOT the only `ρ>0, n<∞` examples (compact weighted manifolds, other Jacobi parameters, simplex diffusions qualify), and Bonnet–Myers alone does not force a compact state space.
## Round 17 (stream F): Riemannian chart, converse of (1.16.8), relaxed completeness, hyperbolic plane (audit R17-Riem)
* PROVED: the converse `Curv ρ ⇒ Ric_g + ∇∇W ≥ ρ g` (`RiemData.riem_ricci_of_curv`) and the equivalence `riem_curv_iff_ricci` (BGL (1.16.8) both directions), `Riemannian/BochnerConverse.lean`. BGL's proof (a test function with prescribed gradient and zero Hessian at the point, then Bochner) goes through with a quadratic polynomial; no richness hypothesis beyond `Curv ρ` (stated for all `C^∞` f).
* PROVED: the bounded co-metric restriction is removed. `EllData.a_bdd` / `RiemData.g_bdd` are replaced by the completeness field `a_exh` / `g_exh` (a nonnegative proper smooth `ψ` with `Γ(ψ) ≤ 1`; implied by the old hypothesis, `exh_of_bdd`). `diff_isComplete` is re-proved from it; the local bound used in the Friedrichs/E2 chain is obtained by compactness (`local_upper`).
* PROVED: second honest example `hypRiem` (hyperbolic plane in the global chart `(x,t)`, co-metric `diag(e^{2t},1)`, unbounded: `hypRiem_g_unbounded`; non-conformal, K = -1) with weight `W = 2 cosh d`: `Ric = -g`, `∇∇W = 2 cosh d · g`, `Curv ρ ↔ ρ ≤ 1` (sharp, via the converse), and unconditional Poincaré, spectral gap, decay, `CD(1,∞)`, `LS(1,0)`, gradient bound (`Riemannian/HypUnconditional.lean`).
* NOT done: multi-chart manifolds and compact manifolds without boundary (spheres): the framework is a single global chart `ℝ^d` with the coordinate formulas of the book; the sphere in stereographic coordinates is a chart of `S^d` minus a point (incomplete: the `g_exh` field fails). No atlas/transition-map formalisation; `g_exh` is the standard sufficient criterion for completeness (a proper function of bounded gradient), not proved equivalent to Riemannian geodesic completeness.

## Round 17 merge: net status after independent hostile audits
Closed: joint time-measurability and `MarkovProcessBridge` for Feller kernels (circle, zonal S³); sharp Sobolev `k > m + d/2` (all `d`; chain shortening only for `d ≥ 3`); converse of (1.16.8) and relaxed completeness (`a_exh`/`g_exh`), hyperbolic plane with `Curv ρ ↔ ρ ≤ 1`.
[SUPERSEDED by Round 18 below: `Core2` now holds for 1-D Gibbs under `GrowHess` and for `ℝ^d` Gibbs under `BddHess3`, both with `ρ>0` witnesses] Partial (Round 17): `Core2` for 1-D Gibbs with bounded `V',V'',V'''` — only `ρ ≤ 0` (hypotheses contradict for `ρ > 0`, ERRATA R17-M1); **Round 18 (stream A2) extends this to `|V''|,|V'''| ≤ C(1+|V'|)` (`GrowHess`), any `ρ`, including `ρ > 0` (`x²/2 + ½cos x`, `x⁴/4 + x²/2`), see below**; still open for `V` outside `GrowHess`, general smooth `V`, `R^d`. Exact Chapman–Kolmogorov without Feller: countable times only.
NOT closed: non-compact finite-`n` CD instance (SphereOpen is cosmetic, ERRATA R17-M2/M3); non-compact Riesz–Markov extension; `ρ < 0` finite-`n` LSI (no such BGL theorem); multi-chart manifolds.

## Round 18, Stream A3: `Core2` and the unconditional converse of Prop 3.3.17 for Gibbs measures on `ℝ^d`
PROVED (`Instances/GibbsRd/Core2Rd*.lean`, `STATEMENTS_R18_Core2Rd.md`, `BGL/AUDIT_R18_CORE2RD.md`): for `G : GibbsRdData d` with `G.BddHess3` (`∂ᵢ∂ⱼV`, `∂ᵢ∂ⱼ∂ₖV` bounded; `∇V` NOT assumed bounded) `GibbsRdData.gibbsRd_core2 : G.gibbsRdFull_unconditional.Core2`, hence
`gibbsRd_mem_domain_of_Γ₂` (converse of Prop 3.3.17) for every `ρ ∈ ℝ` with `HessGe V ρ`.  This class contains `ρ > 0` (it supersedes the vacuity of the 1-D `BddJet` class for `ρ > 0`, ERRATA R17-M1, but only in `ℝ^d`): `gaussData d` (`ρ=1`) and the non-Gaussian `cosData d`, `V = |x|²/2 + cos(x₀)/2` (`ρ = 1/2`).
Proof: smooth resolvent solution via `ellReg`; `∇v, ∇²v ∈ L²` by cut-off Caccioppoli / cut-off Bochner (only `Hess V ≥ ρ` and `|Lχ_n| ≤ K` used); commutator expansions `L(χv)`, `L²(χv)` with uniformly bounded coefficients (scaling of `cut` + linear growth of `∇V`).
**Still open (exact):** `Core2` for `GibbsRdData` with unbounded `Hess V` or `∇³V` (e.g. `V = |x|⁴`); for arbitrary `EllData d` / `RiemData d` (commutators involve `∂a` and `a` itself; not attempted); for arbitrary smooth `V` (≡ e.s.a. of `L²` on `C_c^∞`).  The 1-D case without `BddJet` is Stream A2's (not touched here).


## Round 19, Stream A5: `Core2` and the unconditional converse of Prop 3.3.17 on `ℝ^d` WITHOUT bounded `∇²V`, `∇³V`
PROVED (`Instances/GibbsRd/Core2RdW*.lean`, `STATEMENTS_R19_Core2Rd.md`, `BGL/AUDIT_R19_CORE2RD.md`): for `G : GibbsRdData d` with `HessGe G.V ρ` (any `ρ`) and `G.GrowHess3`
(`|∂ᵢ∂ⱼV|, |∂ᵢ∂ⱼ∂ₖV| ≤ C(1 + Σ|∂ₗV|)`): `GibbsRdData.gibbsRd_core2_w`, `gibbsRd_mem_domain_of_Γ₂_w` (supersedes `BddHess3` of R18, which implies `GrowHess3`).
Route (BGL §3.2 Caccioppoli cut-offs, Prop 3.3.17): `Hess v ∈ L²` by cut-off Bochner without `Lχ` (`memLp_hess_resolvent_free`), weighted jets `∂ₖV v`, `∂ₖV ∂ᵢv`, `∂ⱼV∂ₖV v ∈ L²` by the `d`-dim. Hardy estimate (`memLp_V_mul_of_hardy`), commutators `Lχ_n`, `∂Lχ_n`, `LLχ_n` handled as `Good × weighted jet` (`ZL_Lchi`, `ZL_dLchi`, `ZL_LLchi`, `cutoff_ZL_w`).
Non-vacuous `ρ = 1 > 0` witness OUTSIDE `BddHess3`: `quarData d`, `V = Σ xᵢ⁴/4 + xᵢ²/2` (`quarData_witness`, `quarData_core2`, `quarData_mem_domain_of_Γ₂`).
**Still open (exact):** `Core2` for `GibbsRdData` with only `HessGe V ρ` (no growth control of `∇²V`, `∇³V` by `∇V`; e.g. `V` convex with `∂²V/|∇V|` unbounded, `e^{|x|²}`-type), neither proved nor refuted; arbitrary smooth `V`; `EllData d`/`RiemData d`.  The radial quartic `|x|⁴/4+|x|²/2` satisfies `GrowHess3` (hand check) but is not formalised (the formal witness is the separable `Σxᵢ⁴/4+xᵢ²/2`).
