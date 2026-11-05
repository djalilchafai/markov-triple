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
**Round 19 (Stream A4, `Instances/Gibbs/Core2Poly*.lean`, `STATEMENTS_R19_Core2.md`, `BGL/AUDIT_R19_CORE2.md`):** `GrowHess` is replaced by the strictly weaker
`PolyHess` (`V'' ≥ -Cw(1+|V'|)` [implied by `V'' ≥ ρ`], `V'' = o(V'²)`, `|V'''| ≤ C(1+|V'|^N)`): `GibbsData.gibbsFull_core2_of_polyHess`, `gibbs_mem_domain_of_Γ₂_polyHess`
(and `_convex`), via the weighted cascade `V'^n v, V'^n v' ∈ L²` (`resolvent_pow_L2`; BE-w + Hardy-w).  Witness outside `GrowHess` with `ρ = 2 > 0`: `V = e^{x²}` (`expGibbs_*`).
**Still open (exact):** `Core2` for 1-D Gibbs when `V'''` is not polynomially dominated by `V'` or `V''` is not `o(V'²)` (the cut-off proof needs `V'''v, V'V''v ∈ L²`, which no `Γ₂`-integrated estimate gives), for arbitrary smooth `V`
(equivalent to e.s.a. of `L²` on `C_c^∞`, neither proved nor refuted; e.s.a. of `L` itself holds for every `V`, Gaffney/BGL 3.2.1), and for `EllData`/`GibbsRdData` on `ℝ^d` (needs `∇²v ∈ L²(μ)` by a cut-off Bochner estimate and the
`d`-dimensional commutators of `L²` with cut-offs).

**Round 18-19 update (`ℝ^d`, `EllData`, `RiemData`).**  R18-A3 proved `Core2` for `GibbsRdData` under `BddHess3` (`Instances/GibbsRd/Core2Rd*.lean`).
**Round 19 (Stream A6, `Instances/GibbsRd/Core2Ell*.lean`, `Instances/Riemannian/Core2Riem*.lean`, `STATEMENTS_R19_Core2Ell.md`, `BGL/AUDIT_R19_CORE2ELL.md`, ERRATA R19-Ell-*):**
`Core2` and the UNCONDITIONAL converse of 3.3.17 are PROVED for every `EllData d` and `RiemData d` under (i) `Curv ρ` (some `ρ ∈ ℝ`) and (ii) `CoreCut`, a cut-off family with
uniformly bounded `Γχ_n, Lχ_n, L²χ_n, Γ(Lχ_n), Γ₂(χ_n)` (`EllData.ell_core2`, `ell_mem_domain_of_Γ₂`, `RiemData.riem_core2`, `riem_mem_domain_of_Γ₂`).  Gibbs `BddHess3` is recovered;
sufficient condition `RadialJets` (T6); non-vacuous with `ρ>0` including the non-flat variable-metric conformal plane `confRiem` (`confRiem_core2`, `Curv 2`).
**Still open (exact):** `CoreCut` for general coordinate data (no theorem from bounds on `∂a, ∂²a, ∂³a, ∇log w`; only radial-in-`ψ` data and flat Gibbs are derived);
the hyperbolic plane `hypRiem` (`W = 2cosh d`) provably has NO `CutFamily` (by-hand Mills-ratio argument in the audit), so `Core2` for it is open; the 1-D/radial quartic Gibbs
has no `CutFamily` either (its `Core2` is R18-A2's different route; the `ℝ^d` quartic is open); arbitrary smooth data remains open.

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

## Round 19 merge: net status of `Core2` (see ERRATA R19-M1)
PROVED (each with a nonvacuous ρ>0 witness and an independent hostile audit): 1-D Gibbs under `PolyHess`; `ℝ^d` Gibbs under `HessGe V ρ` + `GrowHess3`; `EllData`/`RiemData` under `Curv ρ` + `CoreCut` (`confRiem`).
OPEN: `Core2` for general smooth `V` with `V'' ≥ ρ` only (e.s.a. of `L²` on `C_c^∞`); 1-D `V'''` not polynomially dominated by `V'` or `V''` not `o(V'²)`; the hyperbolic plane (`hypRiem` has no `CoreCut`; `Core2` open); a general jet criterion for `CoreCut` (only `RadialJets` proved).

## Round 20, Stream D3: converse of Prop 3.3.17 WITHOUT `Core2` (abstract)
## DIFFERENCE FROM BGL
BGL's converse uses the tacit `L²`-core step (`Core2`, ERRATA R15-1).  `FullTriple.mem_domain_of_Γ₂_direct` (`Extension/ConverseDirect.lean`) does not: it shows `Lf ∈ L²` for
`f ∈ 𝒜`, `Γ(f), Γ₂(f) ∈ L¹` by the BGL Prop. 3.2.1 cut-off technique applied to `Γ₂` (identity `cutoff_Γ₂_identity`; cross term by `hessCS`, from BGL (3.3.7); Fatou), then ESA (`mem_domain_of_maximal`).
Hypotheses: ESA (F10), completeness (Def 3.3.9), `CD(ρ,n)`; no `Core2`, no ergodicity, no growth/`CoreCut`; no extra hypothesis `HessCS`.  PROVED unconditionally in the abstract framework.
Applied (`ConverseDirectInst.lean`): OU (incl. concrete `f = id`), circle, Lebesgue, and EVERY `EllData d`/`RiemData d` with `Curv ρ` (no `CoreCut`).  See `AUDIT_R20_CONVERSEDIRECT.md`, ERRATA R20-D3-*.
**Still open:** `Core2` itself (e.s.a. of `L²` on `𝒜₀`) is NOT obtained and not needed for the converse; any statement that needs `Core2` (e.g. other uses of `core2_of_dense`) is unchanged.  The direct theorem needs `CD(ρ,n)` on all of `𝒜` and completeness; for abstract triples that are not complete the converse is still conditional on `Core2`.
## Round 20, Stream D2: the converse of Prop 3.3.17 for `EllData`/`RiemData` WITHOUT `Core2`/`CoreCut`
DIFFERENCE FROM BGL: BGL (p. 161-162) proves the converse through `Core2` (density of `(L²+Id)𝒜₀`, silently used, ERRATA R15-1; R19: only under `Curv ρ` + `CoreCut`).  Here (`Instances/GibbsRd/DirectEll*.lean`,
`Instances/Riemannian/DirectRiem*.lean`, `STATEMENTS_R20_DirectEll.md`, `AUDIT_R20_DIRECTELL.md`) the converse is proved under `Curv ρ` ONLY: `Lf ∈ L²` by the cut-off identity
`∫χ²(Lf)² = ∫χ²Γ₂(f) + ∫χΓ(χ,Γf) − 2∫χLfΓ(χ,f)` (BGL Prop 3.2.1 style, completeness cut-offs `Γχ ≤ 1`, no `Lχ`, `Γ₂(χ)`), the cross term by the Hessian Cauchy–Schwarz
`Γ(u,Γf)² ≤ 4Γ(u)Γ(f)(Γ₂(f) − ρΓ(f))` (Bochner + `Ric + ∇∇W ≥ ρ g`), then the existing `FullTriple.mem_domain_of_ESA` (F10).
PROVED: `EllData.ell_mem_domain_of_Γ₂_direct`, `RiemData.riem_mem_domain_of_Γ₂_direct`, `hypRiem_mem_domain_of_Γ₂_direct` (the hyperbolic plane, `Curv 1`, no `CoreCut`; first converse of 3.3.17 on it), `confRiem_mem_domain_of_Γ₂_direct`.
STILL OPEN: `Core2` itself for `hypRiem` and for general smooth `V` (the direct route does not give it); the abstract converse for a general Full triple (conditional on `Core2`, or on `Lf ∈ L²` via `mem_domain_of_ESA`); the Gibbs 1-D / `ℝ^d` direct versions (other stream).

## Round 20 merge: the converse of Prop 3.3.17 no longer needs `Core2` for complete triples (ERRATA R20-M1)
PROVED: `FullTriple.mem_domain_of_Γ₂_direct` (abstract, completeness + `CD ρ n`), `EllData`/`RiemData` under `Curv ρ` (hyperbolic plane included). DIFFERENT FROM BGL's proof (see each file's `## DIFFERENCE FROM BGL`). All earlier statements in this file saying the converse is 'open' / 'conditional on `Core2`' are SUPERSEDED for complete triples. STILL OPEN: `Core2` itself for general `V`; converse for non-complete abstract triples.
## Round 20, Stream D1: converse of Prop 3.3.17 for Gibbs WITHOUT `Core2` (see ERRATA R20-D1-*, `Instances/Gibbs/STATEMENTS_R20_Direct.md`, `BGL/AUDIT_R20_DIRECT.md`)

**DIFFERENCE FROM BGL.**  BGL's converse proof needs `𝒜₀` a core for `L²` (`Core2`, ERRATA R15-1).  New route (not the book's): essential self-adjointness of `L` (F10; BGL Prop. 3.3.6 (i),
`FullTriple.mem_domain_of_ESA`) + a cut-off Caccioppoli estimate on `Γ₂` (technique of BGL Prop. 3.2.1) showing `Lf ∈ L²` from `Γ(f), Γ₂(f) ∈ L¹` and `V'' ≥ ρ`.
PROVED (axioms `propext`, `Classical.choice`, `Quot.sound`): `GibbsData.gibbs_mem_domain_of_Γ₂_direct` (1-D, hypothesis `∀x, ρ ≤ V''` only) and
`GibbsRdData.gibbsRd_mem_domain_of_Γ₂_direct` (`ℝ^d`, `HessGe V ρ` only), same conclusion shape as the `Core2`-based theorems; no growth condition on `V`.  Witnesses with `ρ>0` outside
`BddJet`/`GrowHess`/`PolyHess` (1-D `spikyGibbs`) and outside `GrowHess3`/`BddHess3` (`ℝ^d` `spikyData`).
**`Core2` is not needed** for the converse of 3.3.17 for Gibbs triples; the `Core2*` results remain as independent facts.  This closes the "R19-Rd-2: `HessGe V ρ` only NOT achieved" item FOR THE CONVERSE.
**Still open (exact):** `Core2` itself for general smooth `V` (ESA of `L²` on `C_c^∞`); the converse of 3.3.17 for `EllData`/`RiemData` beyond `Curv ρ`+`CoreCut` (variable metric: the Hessian bound for the
cross term is not abstracted), and for a general `FullTriple` (still conditional on `Core2`, `FullTriple.mem_domain_of_Γ₂`).

## Round 20 final merge: converse of Prop 3.3.17 (ERRATA R20-M1, R20-M3)
The converse of BGL Prop 3.3.17 holds WITHOUT `Core2` and without growth conditions for: every complete `FullTriple` with `CD ρ n`; every `EllData d`/`RiemData d` with `Curv ρ` (hyperbolic plane included); 1-D `GibbsData` with `V'' ≥ ρ`; `GibbsRdData d` with `HessGe V ρ`. Each proof DIFFERS FROM BGL (cut-off Γ₂ identity + ESA of `L`, not the L²-core step). The Round 17-19 `Core2` classes (`GrowHess`, `PolyHess`, `GrowHess3`, `CoreCut`) are independent facts about essential self-adjointness of `L²`. OPEN: `Core2` for general `V`; converse for non-complete abstract triples.

## Round 21: non-complete triples (ERRATA R21-1..R21-4)
* PROVED (`Instances/Interval`): `ivDiff`, `Γ₂ = (Lf)²`, `iv_not_complete`, `iv_not_esaProp`, `iv_no_fullTriple`. This is a non-complete `DiffusionTriple`, NOT a `FullTriple`.
* OPEN: a non-complete `FullTriple` with CD (the zonal Gegenbauer triple on `(-1,1)` with `C_c^∞`, `λ ≥ 3/2`: needs the weighted triple and ESA on `C_c^∞`; high effort), bounded `(a,b)` and general bounded `Ω ⊂ ℝ` (affine transport / larger).

## Round 22: net status (ERRATA R22-*)
* CLOSED: bounded open `Ω ⊂ ℝ` non-complete/non-ESA `DiffusionTriple`s (R21 `I5`); non-compact Riesz–Markov kernel representation for FINITE `μ` (sub-Markov kernels); a non-compact finite-`n` CD `FullTriple` exists (`lebesgueFull`, `ρ ≤ 0`); the two Round 20 witness leftovers (weak, bounded `f`).
* OBSTRUCTIONS (formal, not goals reached): `RadialJets` fails for `V`, `log(1+V)` on the hyperbolic plane; `KernelRepresentation` + sub-invariance does not imply exact CK.
* OPEN: a non-complete `FullTriple` with CD (Gegenbauer `λ ≥ 3/2`: `goDiff` built, F8/F10 and the remaining fields missing); Riesz–Markov for infinite `μ`, Markov (conservative) kernels, Feller extension, and an exact all-time semigroup for abstract compact triples; `CoreCut`/`Core2` for the hyperbolic plane (by hand false for the radial route, not formalised); atlas gluing (≈2500–4000 lines); `(ℝ^d, Lebesgue)`, `d ≥ 2`, as a `FullTriple`; `Core2` for general smooth `V`.

## Round 23: net status (ERRATA R23-*)
* CLOSED: a non-complete `FullTriple` with CD exists (`goFullTriple`, zonal Gegenbauer `λ = 3/2`; ERRATA R23-F-1); F10 for it (`go_esaProp`); non-compact Riesz–Markov kernel representation for infinite `μ` finite on compacts (per-`t`, a.e., sub-Markov; Markov kernels for `StandardTriple`s; instance `lebesgueFull`), without Feller / Chapman–Kolmogorov / `MarkovProcessBridge`.
* (Superseded by Round 24 Stream A below: F8, F10, S10, S11 for `(ℝ^d, Lebesgue)` are now proved.) `(ℝ^d, Lebesgue)` was a `DiffusionTriple` with exact pointwise Bochner range `ρ ≤ 0 ∧ d ≤ n` and fields F1–F7, F9.
* OPEN: (`FullTriple` on `ℝ^d`: CLOSED in Round 24 Stream A); Feller extension, Chapman–Kolmogorov and a `MarkovProcessBridge` for infinite `μ`; exact all-time semigroup for abstract compact triples; `Core2` for general smooth `V` (R23-F-1 suggests it is not a consequence of F1–F10 + CD, not formalised); `CoreCut`/`Core2` for the hyperbolic plane; atlas gluing; converse of Prop 3.3.17 for non-complete triples (now known to be a genuine question for `goFullTriple`: completeness-free converse, `mem_domain_of_Γ₂` needs `Core2`).

## Round 24, Stream A: `FullTriple` on `(ℝ^d, Lebesgue)` CLOSED (d ≥ 1)
`lebesgueRdFull d hd : FullTriple (Fin d → ℝ)` (`Instances/LebesgueRd/Full/Main.lean`), F8/F10/S10/S11 proved via the Gaussian heat flow (strong L² derivative, Duhamel identification `semigroup_eq_heatRd`); `lebesgueRdFull_CD_iff : CD ρ n ↔ ρ ≤ 0 ∧ d ≤ n`; finite-measure counterpart `gaussRdFull` (CD 1 ∞). DIFFERENCE FROM BGL: F10/S10 by a heat-flow ODE argument, not Weyl's lemma (the `EllData` regularity chain is for probability measures). Still open: converse of Prop 3.3.17/Core2 not examined for this triple; `d = 0` excluded (point space).
* PARTIAL: `(ℝ^d, Lebesgue)` is a `DiffusionTriple` with exact pointwise Bochner range `ρ ≤ 0 ∧ d ≤ n` and fields F1–F7, F9; missing F8, F10, S10, S11 to be a `FullTriple`.
* OPEN: `FullTriple` on `ℝ^d`; Feller extension, Chapman–Kolmogorov and a `MarkovProcessBridge` for infinite `μ`; exact all-time semigroup for abstract compact triples; `Core2` for general smooth `V` (R23-F-1 suggests it is not a consequence of F1–F10 + CD, not formalised); `CoreCut`/`Core2` for the hyperbolic plane; atlas gluing; converse of Prop 3.3.17 for non-complete triples (now known to be a genuine question for `goFullTriple`: completeness-free converse, `mem_domain_of_Γ₂` needs `Core2`).

## Round 24 (stream B)
* CLOSED: converse of Prop 3.3.17 for `goFullTriple` and every `FullTriple` with `CD(ρ,n)`, `n<∞` (ERRATA R24-B-1), no completeness/Core2.  STILL OPEN: `n=∞` without completeness (and without Core2).
* OPEN (superseded in part by Round 24 stream C below: Feller extension and CK for infinite `μ` are now closed conditionally on `IsFellerC0`): `FullTriple` on `ℝ^d`; Feller extension, Chapman–Kolmogorov and a `MarkovProcessBridge` for infinite `μ`; exact all-time semigroup for abstract compact triples; `Core2` for general smooth `V` (R23-F-1 suggests it is not a consequence of F1–F10 + CD, not formalised); `CoreCut`/`Core2` for the hyperbolic plane; atlas gluing; converse of Prop 3.3.17 for non-complete triples (now known to be a genuine question for `goFullTriple`: completeness-free converse, `mem_domain_of_Γ₂` needs `Core2`).

## Round 24, stream C (stochastic layer; see `Stochastic/R24/STATEMENTS_R24_C.md`)
* CLOSED (conditional on the Feller hypothesis): for `T` with `μ` finite on compacts (infinite allowed), full support and `IsFellerC0 T`
  (`P_t` maps `C_c` into `C_0`): everywhere-defined kernels `fellerKernelInf` with exact Chapman–Kolmogorov (all `s,t,x`), `κ_0 = id`,
  `μ.bind κ_t ≤ μ`, representation on bounded measurable `L²`, joint measurability in `(t,x)`, `MarkovProcessSemigroupData`, and
  (under pointwise `κ_t(x,X)=1`) `MarkovProcessBridge`.  Instances: every `IsFeller` compact triple (circle, zonal `S³`; agrees with R16
  kernels), OU on `ℝ` (non-compact, finite `γ`).
* CLOSED (characterisation): for compact full-support triples, exact all-time CK for a kernel representation holds iff it is weakly
  continuous (= Feller): `isFeller_iff_exists_continuous_kernel`, `weakFeller_add`; with R22-E3-2 this pins down the extra hypothesis.
* OPEN: an infinite-`μ` instance of `IsFellerC0` (heat semigroup of `lebesgueFull`: needs heat-kernel identification); deriving
  `κ_t(x,X)=1` for every `x` from conservativity; non-full-support `μ`; whether a non-Feller `P_t` can have an exact all-time kernel
  semigroup (neither proved nor refuted); Feller itself from the triple axioms.
## Round 24, Stream D: `Core2` and the BGL route (ERRATA R24-D-*; `Instances/Riemannian/R24/STATEMENTS_R24_D.md`)
PROVED: (i) `FullTriple.core2_iff_dense`, `core2_orth` (abstract duality form of `Core2`); (ii) **`GegenbauerOpen.goFullTriple_not_core2`**: the non-complete triple `goFullTriple` (F1–F10, `CD(3,4)`) does NOT satisfy `Core2`, so `Core2` is not a consequence of F1–F10 + `CD` and the book's tacit step (R15-1) is genuinely extra for non-complete triples (`exists_fullTriple_cd_not_core2`); the deficiency pair is explicit (power series `w` with `L w = w`, `h = (Λ/4) log(1-x²)`, `w - L h ∈ L²`); (iii) `hyp_core2_route_status`: for `hypRiem` (`Curv 1`, `CD(1,∞)`), all hypotheses of the `Curv ρ + CutFamily` route hold except the cut-off family; `RadialJets` fails for `V`, `log(1+V)`.
STILL OPEN (exact): `Core2` for `hypRiem` and any COMPLETE triple with CD; `hypRiem.toEll.CoreCut` (false by hand, AUDIT_R19 §6, not formalised); `Core2` for general smooth `V`.  No abstract BGL theorem "completeness + `CD(ρ,∞)` ⇒ `Core2`" is available: `Γ₂ ≥ ρΓ` gives no bound on `Lχ_n`.

## Round 25, Stream F: `Core2` on `ℝ^d` (ERRATA R25-F-*; `Instances/LebesgueRd/Core2/STATEMENTS_R25_F.md`)
PROVED: `LebesgueRd.lebesgueRdFull_core2 (hd : 1 ≤ d)` (infinite measure; `(1-Δ)²C_c^∞` dense in `L²(ℝ^d)`), `gaussRdFull_core2` (R18 theorem under the R24 name), and the
`Core2`-based converse of Prop 3.3.17 `lebesgueRdFull_mem_domain_of_Γ₂` (all `CD ρ n`, `ρ ≤ 0`, `d ≤ n ≤ ∞`).  DIFFERENCE FROM BGL: BGL never states `Core2`; the route is the heat-flow
ODE argument of R24-A (F10) one order up: fourth-order cut-off (`cutoff4_graph_aux`) transports `w ⟂ (1-L)²𝒜₀` to `heat_a φ`, then `H = G₁ - G₀`, `H' = aH` bounded forces `w = 0`.
STILL OPEN (exact): `Core2` for `hypRiem` and any complete triple with `CD(ρ,∞)` in the abstract (no BGL theorem; `Γ₂ ≥ ρΓ` gives no bound on `Lχ_n`, `LLχ_n` needed by the
fourth-order cut-off); `Core2` for general smooth `V`.  Nothing is claimed for `hypRiem`.  Superseded OPEN lines about `Core2` on `(ℝ^d, Lebesgue)` ("converse not examined for this triple" in Round 24 Stream A) are closed by this stream.
## Round 25, Stream E: first infinite-`mu` instance of the stochastic layer (ERRATA R25-E-*; `Stochastic/R25/STATEMENTS_R25_E.md`)
* CLOSED (annotates, does not delete, the R24-C OPEN lines on infinite-`mu` instances): `(ℝ^d, Lebesgue)` (`lebesgueRdFull d hd`) is `C_0`-Feller (`R25.lebesgueRd_isFellerC0`; `semigroup_eq_heatRd` extended from `C_c^∞` to `C_c` by symmetry of the Gaussian and density, `lebesgueRd_semigroup_cc`); the abstract kernels `fellerKernelInf` equal `N(x, 2t I_d)` at every `x` (`fellerKernelInf_lebesgueRd`, `heatKernelRd_apply_pi`); pointwise mass one (`lebesgueRd_hM`); exact Chapman-Kolmogorov (`heatKernelRd_add`, via the abstract `fellerKernelInf_add`); `volume` invariant (`heatKernelRd_bind`); `brownianBridgeRd : MarkovProcessBridge` for Brownian motion with infinite invariant measure.
* General mass statement: S11 + `IsFellerC0` give mass one a.e. and a lower semicontinuous mass function; this does not give mass one at every point (`fellerKernelInf_univ_ae`, `_univ_lsc`, `_deficit_null_Fsigma`). The extra hypothesis that works is continuity of `x |-> kappa_t(x,X)` (`fellerKernelInf_univ_eq_one_of_continuous`, `fellerMarkovProcessBridgeInf_of_continuous`). OPEN: whether S11 + Feller (no continuity hypothesis) implies mass one everywhere (neither proved nor refuted).
* Finite-`n` converse of Prop. 3.3.17 for `lebesgueRdFull` (`lebesgueRdFull_mem_domain_of_Γ₂_finite`).
* OPEN / not done: a direct Gaussian-convolution proof of Chapman-Kolmogorov (CK is obtained from the abstract exact CK plus the identification); Feller/Markov bridge for infinite-`mu` Gibbs triples other than `ℝ^d` Lebesgue; the `d = 0` case (not a `lebesgueRdFull`).
## Round 26, Stream I: `Core2` (ERRATA R26-I-*; `Theory/Extension/R26/STATEMENTS_R26_I.md`)
* PROVED: `FullTriple.core2_iff_orth` (`Core2` iff no nonzero `L^2` vector is orthogonal to `(1-L)^2 A_0`: the exact shape of a counterexample); `FullTriple.core2_of_eigen` / `core2_of_eigen'` (an `A_0` containing eigenfunctions of `L` with eigenvalue `-c`, `c >= 0`, whose classes span a dense subspace of `L^2`, gives `Core2`); `Sphere.sFull_core2` (compact zonal `S^3`, Chebyshev eigenfunctions).
* NOT done (honest): no abstract theorem `IsComplete + CD(rho,n) => Core2`; `Core2` for `hypRiem` remains OPEN (nothing claimed); the abstract `FullTriple` has no hypoellipticity/resolvent-regularity, and a fourth-order cut-off needs control of `L L zeta`, `Gamma(zeta,Gamma(zeta,.))`, `Gamma_2(zeta,b)`.  Abstractly `Core2` is ESA of `L^2` on `A_0` and is not implied by ESA of `L` (the non-complete `goFullTriple` has F10 but not `Core2`).
* Gegenbauer family (`C_c^infty((-1,1))`, only `lambda = 3/2` formalised): heuristic Frobenius count (unproved, unformalised) suggests `Core2` fails for `3/2 <= lambda < 7/2` and holds for `lambda >= 7/2`; none of this is a theorem here.
* Not covered: `circleFull` and `ouBFull` `Core2` (the real Fourier / Hermite eigenbases are not packaged as dense in real `L^2` in the repo; the criterion applies once they are).
* R26-I hostile audit note on the Gegenbauer heuristic (still UNPROVED, unformalised; relabelling only): an independent Frobenius count agrees.  With `t = 1-x`, `L ~ 2t d^2 + (2lambda+1) d`, `L t^r = r(2r+2lambda-1) t^(r-1)`, so `(1-L)^2 u = 0` has exponents `0, 1` (analytic) and `1/2-lambda, 3/2-lambda` (singular) at each endpoint; `t^r` is `L^2` for weight `t^(lambda-1/2)` iff `2r+lambda+1/2 > 0`, i.e. `r = 1/2-lambda` iff `lambda < 3/2`, `r = 3/2-lambda` iff `lambda < 7/2` (at `lambda = 3/2` it is a `log` solution).  Hence each endpoint has `>= 3` `L^2` local solutions of the 4-dimensional space for `lambda < 7/2`, two such 3-dim subspaces meet in a nonzero `w` (non-`Core2`, by `core2_iff_orth`), while for `lambda >= 7/2` only the analytic ones survive and `<(1-L)^2 w, w> = ||(1-L)w||^2 = 0` kills them.  Caveats: the statement above is a sketch (log resonances, global gluing and boundary terms not written out); the phrase "Gamma-bounded functions are bounded" is a loose reason for non-completeness (the actual reason: finite Gamma-distance to the endpoints, so no cut-offs with bounded Gamma). The sphere `S^3` is `lambda = 1`, `S^4` is `lambda = 3/2`.
## Round 26, Stream H: atlas gluing, first verified step (ERRATA R26-H-*; `Instances/Riemannian/R26/STATEMENTS_R26_H.md`)
PROVED (BGL Appendix C.3 / Sect. 1.11.3 coordinate formulas): `R26.gamma_chart_change` (any `d`: `Γ_b(F,H)∘τ = Γ_a(F∘τ,H∘τ)` from the pushforward law `g_b∘τ = J g_a Jᵀ`); in `d = 1`, `Chart1` (co-metric `g = x'^{-2}`, `w = x'`), chartwise `Γ`, `L = (1/w)(wgF')'` equal the intrinsic `Gc`, `Lc` of the library circle on `𝒜₀` (`Chart1.Γ_eq`, `L_eq`), hence chart-transition invariance (`chart_transition`); the two stereographic charts of `𝕋` with `g = π²(1+t²)²`, `w = 1/(π(1+t²))` and the transition `τ(t) = -1/t` with `g_S∘τ = τ'² g_N`, `w_N = (w_S∘τ)|τ'|` (`transition_g/_w`, `north_south_pt`); an atlas structure with glued `Γ, L` independent of the chart (`Atlas1.glueΓ_indep/_L_indep`, `stereoAtlas`); the Riemannian measure glued by the partition of unity `cos²(πx), sin²(πx)` equals Haar (`integral_north/_south`, `atlasIntegral_eq`); the `DiffusionTriple 𝕋` `atlasDiff` built from the glued data (`Γ := glueΓ`, `L := glueL`, `μ = μ₀`) with D1-D8, `Γ₂` and `CD(ρ,n)` (`ρ ≤ 0`) computed from the glued `L` (`atlasDiff_Γ₂`, `atlas_CD`).
NOT done (updates the OPEN/NOT-done "atlas gluing" and "multi-chart" lines above, which remain OPEN in general): `L` chart-change invariance for `d ≥ 2` (Piola identity `div(|detJ| J⁻¹V)`), general `Atlas`/manifold structure with `C^∞(M)`, genuine spheres `S^d` (`d ≥ 2`; the library `Sphere` is the zonal one-dimensional reduction) and positive curvature on an atlas manifold, `FullTriple`/semigroup for `atlasDiff` (it agrees with `circleDiffusion` only on `𝒜₀`, so the Friedrichs data are not re-derived), compatibility of `Chart1` with `RiemData`/`EllData` (stereographic charts fail `g_exh`). Plan: (1) Piola identity for general `d` (needs derivative of the cofactor matrix) giving `L` invariance; (2) `Atlas d` with chart domains open in `ℝ^d`, `ContDiffOn` transitions, partition of unity; (3) `S^2` with two stereographic charts, `g = ((1+|x|²)/2)²δ`, check `CD(1,2)` chartwise against `sphere_CD_two_three`-style results; (4) `𝒜₀ = C^∞(M)`, density in `L^p` via partition of unity. Estimate for (1)-(4) remains in the 2500-4000 line range.

## Round 27, Stream K: pointwise mass one; Feller property of `goFullTriple` (ERRATA R27-K-*; `Stochastic/R27/STATEMENTS_R27_K.md`)
* OPEN (annotates the R25-E "neither proved nor refuted" line, still open): does S11 + `IsFellerC0` force `kappa_t(x,X) = 1` at every `x`?  Now known: the pointwise
  deficit is non-increasing in `t`; under `kappa_s(x,.) << mu` it is time-independent for `t > 0`; absolute continuity + pointwise initial condition give mass one
  everywhere and a `MarkovProcessBridge` (`R27.fellerMarkovProcessBridgeInf_of_ac_init`).  No diffusion counterexample, no general proof.
* CLOSED: `goFullTriple` is `C_0`-Feller on `X = R` (`R27.goFull_isFellerC0`), i.e. `P_t[f]` has a continuous version on `[-1,1]`.  STILL OPEN: kernels and a
  `MarkovProcessBridge` for `goFullTriple` (`goMu_not_isOpenPos`: the R24 machinery needs `IsOpenPosMeasure`; needs a transport of the triple to `[-1,1]` / `(-1,1)`).
  [ANNOTATION R28-M: the "STILL OPEN" part is now CLOSED, see "Round 28, Stream M": `R28.goMarkovProcessBridge : MarkovProcessBridge goFullTriple.toDiffusionTriple`.]

NOT done (updates the OPEN/NOT-done "atlas gluing" and "multi-chart" lines above, which remain OPEN in general): `L` chart-change invariance for `d ≥ 2` (Piola identity `div(|detJ| J⁻¹V)`), general `Atlas`/manifold structure with `C^∞(M)`, genuine spheres `S^d` (`d ≥ 2`; the library `Sphere` is the zonal one-dimensional reduction) and positive curvature on an atlas manifold, `FullTriple`/semigroup for `atlasDiff` (it agrees with `circleDiffusion` only on `𝒜₀`, so the Friedrichs data are not re-derived), compatibility of `Chart1` with `RiemData`/`EllData` (stereographic charts fail `g_exh`). Plan: (1) Piola identity for general `d` (needs derivative of the cofactor matrix) giving `L` invariance; (2) `Atlas d` with chart domains open in `ℝ^d`, `ContDiffOn` transitions, partition of unity; (3) `S^2` with two stereographic charts, `g = ((1+|x|²)/2)²δ`, check `CD(1,2)` chartwise against `sphere_CD_two_three`-style results; (4) `𝒜₀ = C^∞(M)`, density in `L^p` via partition of unity. Estimate for (1)-(4) remains in the 2500-4000 line range. [ANNOTATION R27-J: steps (1) Piola, (2) general `Atlas d`, (3) `S²` two-chart atlas (with chartwise coordinate-function computations of `Γ, L, Γ₂`; this is NOT part of (4)) are now PROVED, see "Round 27, Stream J"; the remainder of (4) stays open.]

## Round 27, Stream J: atlas gluing beyond d = 1 (ERRATA R27-J-*; `Instances/Riemannian/R27/STATEMENTS_R27_J.md`)
PROVED (BGL Appendix C.3; all axioms `propext, Classical.choice, Quot.sound`, 0 warnings): (1) the Piola identity `R27.piola_identity` (`Σₖ ∂ₖ (adj Dτ)_{ki} = 0` for `τ ∈ C²`, any `d`; Jacobi's formula `pderiv_det` through `detRowAlternating` as a continuous multilinear map, then Hessian symmetry against determinant antisymmetry) and `Lch_chart_change` (any `d`): `L_b F ∘ τ = L_a (F ∘ τ)` from `g_b∘τ = J g_a Jᵀ`, `w_a = (w_b∘τ)|det J|`, with the sign of `det J` handled locally; `Gch_chart_change`; (2) a general `Atlas M d` and glued `Γ, L, Γ₂` whose chart independence (`glueΓ_indep`, `glueL_indep`, `glueΓ₂_indep`) is deduced from the transition laws only (no global operator), plus `glueΓ_smooth`, `glueL_smooth`; (3) `sphereAtlas : Atlas S2 2` (two stereographic charts, co-metric `((1+|y|²)/2)² δ`, `w = 4/(1+|y|²)²`, transition `y ↦ y/|y|²`, `det J = -|y|⁻⁴`) with all fields (open overlaps, `C²` transition, pushforward laws, covering of `S²`) proved; (4) chartwise `L p_a = -2 p_a`, `Γ(p_a,p_b) = δ_ab - p_a p_b`, `Γ₂(p_a) = 1 + p_a²` for the coordinate functions, identical in both charts and glued (`sphere_glueL_coord`, `sphere_glueΓ_coord`, `sphere_glueΓ₂_coord`), hence `CD(1,2)` with equality `Γ₂ = Γ + ½ (Lf)²` on `p_a` (`sphere_CD12_coord_eq`).
NOT done (the Round 26 H lines "L invariance for `d ≥ 2`", "general Atlas", "genuine spheres `S^d`" are now CLOSED for `L`-invariance, the algebraic atlas notion and `S²`; the rest stays OPEN): `CD(1,2)` for ALL `f` on `S²` (needs the chartwise Bochner formula `Γ₂ = |Hess f|² + Ric(∇f,∇f)` for the conformal co-metric, i.e. `riem_bochner` without `g_exh`, or a direct computation of `Γ₂ - Γ - ½(Lf)²` in the conformal chart); topology and smooth structure on `M` (`Atlas` is purely algebraic: no continuity of `pt`, no Hausdorff property); `C^∞(M)` as `𝒜₀` and density in `L^p`; the Riemannian measure of `S²` glued by a partition of unity; a `DiffusionTriple`/`FullTriple` on `S²` built from the glued data and its semigroup (`D1-D8`, `Core2`); `S^d` for `d ≥ 3` (needs the inversion `y/|y|²` in `Fin d` coordinates; `piola_identity` and `Lch_chart_change` are already for all `d`) and weights `e^{-W}`. [ANNOTATION R28-L: the genuine round sphere `S^{n-1} ⊂ ℝ^n` (`n ≥ 2`) as a `DiffusionTriple` with `CD(n-2,n-1)` pointwise (Γ₂ inequality for all `f ∈ 𝒜₀ = C^∞(S^{n-1})`) is now PROVED by a different route (degree-0 homogeneous extension to `ℝ^n`, no atlas), see "Round 28, Stream L"; the atlas-based `S^d` for `d ≥ 3` and the `FullTriple`/semigroup remain open.]
Plan: (a) `CD(1,2)` inequality: in the conformal chart `g = ρδ`, `ρ = ((1+|y|²)/2)²`, `w g = 1` for `d = 2`, so `L = ρ Δ`; compute `Γ₂ - Γ - ½(Lf)²` (third derivatives cancel) as a nonnegative quadratic form in `∂²f` (estimate 400-700 lines); (b) `DiffusionTriple S2` from `sphereAtlas.glueΓ/glueL` on `𝒜₀ = {f | ∀ k, sphereAtlas.Smooth k f}` with `μ` from `w dy` and a partition of unity (needs a measurable structure on `S2`, about 800 lines); (c) compare with the library zonal `Sphere` through the height function `p_2`.

## Round 28, Stream M: Markov kernels and a `MarkovProcessBridge` for `goFullTriple`; bridge survey (ERRATA R28-M-*; `Stochastic/R28/STATEMENTS_R28_M.md`)
* CLOSED: `R28.goMarkovProcessBridge : MarkovProcessBridge goFullTriple.toDiffusionTriple` on the ORIGINAL space `X = ℝ` (jointly measurable Markov kernels, exact
  Chapman-Kolmogorov, `κ_0 = id`, `goμ` invariant, `rep` on all bounded measurable `L²(goμ)` functions).  Route: restrict to the compact subtype `GI = [-1,1]`, where
  `goμI = goμ.comap val` has full support (`goμI.IsOpenPosMeasure`); restriction `goRestr : L²(goμ) ≃ₗᵢ L²(goμI)`; the conjugated semigroup `goSemigroupI t = goRestr ∘ P_t ∘ goRestr⁻¹`
  (`goSemigroupI_restr`) is conservative (`goSG_one`, S11 via `standardSemigroup_one_fin`) and Feller (`goI_isFeller`: R27 `go_semigroup_poly_cls` + Weierstrass);
  the R16 compact Feller layer (restated for abstract `SGData`, since it only uses the semigroup) gives the kernels `goKernelI` (`goKernelI_isMarkov`, `_zero`, `_add`, `_bind`, joint measurability); they are pushed to `ℝ` (`goKernel`:
  `(goKernelI t x).map val` for `x ∈ [-1,1]`, `δ_x` for `x ∉ [-1,1]`, a `goμ`-null set; the freezing outside is forced by `κ_0 = id` on `ℝ`, see ERRATA R28-M-1).
  The bridge for `goFullTriple` is stated against the original triple; no `DiffusionTriple` on `[-1,1]` was built, only the transported SEMIGROUP data (`SGData`), and the relation to `goFullTriple` is exactly `goSemigroupI_restr` / `goKernel_rep`.
* Extra closure: `R28.ouBMarkovProcessBridge : MarkovProcessBridge ouB` (OU with test algebra `ℬ`; Mehler kernels, `PtB_mehler`).
* Survey: every library `StandardTriple`/`FullTriple`/`CompactTriple` instance and whether it has a `MarkovProcessBridge` (named, against the Standard/Full/Compact triple, in `R28/Survey.lean`):

| instance (space) | has `MarkovProcessBridge`? | construction / reason |
|---|---|---|
| `ouStandard`, `ouFull` (ℝ, γ) | YES | `ouMarkovProcessBridge` (Mehler kernels; `ouStandard_bridge`, `ouFull_bridge`); also `R24.ouMarkovProcessBridgeInf` (Feller route) |
| `ouBStandard`, `ouBFull`, `ouBCompact` (ℝ, γ, `𝒜₀ = ℬ`) | YES (R28) | `ouBMarkovProcessBridge`: Mehler kernels, `PtB_mehler` on `ℬ` + density (`KernelBridge.ofTestClass`) |
| `circleStandard`, `circleFull`, `circleCompact` (𝕋) | YES | `circleMarkovProcessBridge` (heat kernels) |
| `sStandard`, `sFull`, `sCompact` (zonal `S³`, `[-1,1]`) | YES | `sphereMarkovProcessBridge` (compact Feller route) |
| `lebesgueRdFull d hd` (`ℝ^d`, Lebesgue, `d ≥ 1`) | YES | `R25.brownianBridgeRd` (heat kernel; `C_0`-Feller, mass one) |
| `goFullTriple` (ℝ, `goμ` on `[-1,1]`) | YES (R28) | `goMarkovProcessBridge` (this round) |
| `lebesgueFull` (ℝ, Lebesgue, the 1-d R14-era triple) | NO [ANNOTATION R29-O: now YES, `R29.lebesgueFull_bridge`, see "Round 29, Stream O"] | only per-`t` a.e. Markov kernel representation (`R23.lebesgue_exists_markovRep`); a bridge needs `IsFellerC0 lebesgueFull` (identify its Friedrichs semigroup with the heat semigroup; the `Rd` route `lebesgueRdFull 1` is a different triple type, no transport proved) |
| `oStandard`, `oFull` (open zonal `S³`, `(-1,1)`) | NO [ANNOTATION R29-O: now YES, `R29.oStandard_bridge`, `R29.oFull_bridge`; `κ_t(x,{±1}) = 0` is PROVED at every `x`, see "Round 29, Stream O"] | the semigroup is `restrC`-conjugate to the zonal one (`PO_restrC`), but the zonal kernels may charge the poles `{±1}`; exact Chapman-Kolmogorov on `(-1,1)` needs `κ_t(x,{±1}) = 0` for EVERY `x ∈ (-1,1)` (a.e. only is provable by reversibility). Not proved, not refuted; restricting/retracting the kernels breaks exact CK or exact `κ_0 = id` |
| `gibbsStandard_unconditional`, `gibbsFull_unconditional` (ℝ, `e^{-V}`) | NO [ANNOTATION R29-O: still NO; conditional `R29.gibbsFull_bridge_of_feller`, missing hypotheses listed in "Round 29, Stream O"] | infinite or finite non-Gaussian `μ`: no Feller (`IsFellerC0`) theorem; `fellerMarkovProcessBridgeInf` hypotheses not established |
| `gaussRdFull d` (`Rd d`, standard Gaussian, finite measure) [ADDED by R28-M audit: omitted from the original table] | NO [ANNOTATION R29-O: still NO unconditionally; product Mehler kernels proved, conditional `R29.gaussRdFull_bridge_of_rep`] | no `MarkovProcessBridge` found in the library (`R25.brownianBridgeRd` is for `lebesgueRdFull` only); the OU/Mehler kernels on `ℝ^d` would apply but no transport of triples is proved. Also omitted from the table: hypothesis-parametrised families `goStandard/goFull`, `gibbsStandard/gibbsFull`, `gibbsRdFull`, `riemFull`, GibbsRd `EllPI.standard/full` (covered by their `_unconditional`/`goFullTriple` instances) |
| `gibbsRdFull_unconditional`, `fullU` (`Rd d`, Gibbs/elliptic) | NO [ANNOTATION R29-O: still NO; conditional `R29.gibbsRdFull_bridge_of_feller`, `R29.fullU_bridge_of_feller`] | same: no Feller property proved |
| `riemFull_unconditional` (`Rd d`, Riemannian/elliptic data) | NO [ANNOTATION R29-O: still NO; conditional `R29.riemFull_bridge_of_feller`] | same |
| `trivialCompact` (Unit; `BGL/Sanity`) | NO | degenerate sanity triple; `P_t = id` not proved from the Friedrichs construction; nothing to gain |
| `atlasDiff` (𝕋), `sphereAtlas` (S², set-level) | n/a | not Standard/Full triples (DiffusionTriple only / purely algebraic atlas) |

  Product triples and the Laguerre/Jacobi families are NOT in the library (no instances), so there is nothing to survey for them.
* NOT done: a bridge for `oFull`/`lebesgueFull`/Gibbs/Riemannian triples (reasons in the table); a `DiffusionTriple` or `FullTriple` structure on `[-1,1]` for the transported Gegenbauer data (only the semigroup is transported; the Friedrichs naturality under the unitary `goRestr` would need functional-calculus naturality of `rcfc`, not proved); kernel UNIQUENESS statements for `goKernelI` (the Riesz kernels are determined at every point by `goSemigroupI` through weak-Feller uniqueness, `R24.weakFeller_kernel_unique`, but this is not restated for the abstract `SGData`); transition densities / heat-kernel formulas (none claimed: the kernels are abstract Riesz-Markov kernels).
## Round 28, Stream L: the genuine round sphere `S^{n-1} ⊂ ℝ^n` (ERRATA R28-L-*; `Instances/SphereN/STATEMENTS_R28_L.md`)
Not the zonal reduction of `Instances/Sphere/*`: the space is `Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1`, the measure the normalised Mathlib surface measure `σ = (σ0 univ)⁻¹ • σ0`, `σ0 = volume.toSphere` (cone/radial construction). Route chosen (cheapest rigorous): operators defined through the degree-0 homogeneous extension `F̃ = f(y/|y|)` (so `Γ(f,g) = ∇F̃·∇G̃`, `L f = ΔF̃` on `|y| = 1` need no independence-of-extension argument in the definition), `𝒜₀ = {f : F̃ is C^∞ off 0}` (a unital algebra; closed under all smooth `ψ`), Euler/homogeneity relations (`hom_dd`, `euler`), integration by parts from `LebesgueRd.ibp_L` with a radial cut-off `Φ(|y|²)` supported in `1/4 ≤ |y|² ≤ 9/4` and the Mathlib polar decomposition (`measurePreserving_homeomorphUnitSphereProd`); the radial cut-off drops out by Euler (`y·∇F̃ = 0`) and the radial integral `∫ r^{n-1} Φ(r²)/r² dr > 0` cancels.
PROVED (all `propext, Classical.choice, Quot.sound`; 0 warnings, no `sorry`, `AxiomCheckR28L.lean`; about 1850 lines in 14 files):
* (L1) `SphereN.A₀S` (algebra), `A₀S_of_contDiff`, `ΓS_mem`, `LS_mem`; extrinsic formulas `ΓS_extrinsic` (`Γ = ∇F·∇G − (x·∇F)(x·∇G)`) and `LS_extrinsic` (`L f = ΔF − Σ x_i x_j ∂_i∂_jF − (n−1) x·∇F`) for restrictions of `C^∞(ℝ^n)` functions, hence independent of the extension; the intrinsic `L` equals the Laplace-Beltrami operator of BGL C.5.
* (L2) `polar` (polar coordinates for the Lebesgue integral), `ibp_σ0`/`ibp_sphere` (`∫ g L f dσ = −∫ Γ(f,g) dσ`), `σ_isProbabilityMeasure`, and `sphereDiffusion n hn : DiffusionTriple (Sph n)` (`2 ≤ n`; D1-D8 all theorems: density by Stone-Weierstrass on the coordinate functions + `C(S)` dense in `L^p`, `comp_mem`, `diffusion` by the chain rule, `integral_L` from `ibp` with `g = 1`).
* (L3) `LS_mul` (`L(fg) = f Lg + g Lf + 2Γ(f,g)`), `ΓA_eq_ΓS` (the book's formula `Γ = ½(L(fg) − fLg − gLf)` agrees with `ΓS` everywhere), `Γ₂_formula` (`Γ₂(f) = |Hess F̃|² + (n−4) Γ(f)` on the sphere, from the Euclidean Bochner identity `LebesgueRd.Γ₂_eq` and the radial weights `ext (Γ f) = |y|²|∇F̃|²`, `ext (L f) = |y|² ΔF̃`), `hess_ineq` (`Σ H_ij² ≥ 2|w|² + (tr H)²/(n−1)` for symmetric `H` with `H y = w ⊥ y`), and `sphere_CD`: `(n−2) Γ(f) + (1/(n−1)) (Lf)² ≤ Γ₂(f)` pointwise on the sphere for every `f ∈ 𝒜₀` (this is `CD(n−2, n−1)`; `n = 3` gives `CD(1,2)` for the round `S²` for ALL `f`, which the atlas stream R27-J had only for coordinate functions). Equality is not claimed.
NOT done / obstructions (precise):
* (L4) [SUPERSEDED in part by Round 29, Stream N below: `sphereStandard` (S10, S11) and F10 are now proved; only F8 remains] `FullTriple`/`StandardTriple`/semigroup for `sphereDiffusion`: NOT attempted beyond the `DiffusionTriple`. Missing pieces: F8 (the Friedrichs semigroup preserves `𝒜 = C^∞`: needs heat-kernel/spectral regularity, i.e. spherical-harmonic decomposition of `L²(S^{n-1})`, not formalised); F10 / `Core2` (via `core2_of_eigen` one needs eigenfunctions of `L` spanning a dense subspace: restrictions of harmonic homogeneous polynomials are eigenfunctions with eigenvalue `−k(k+n−2)`, but density of their span in `L²` needs the Fischer/harmonic decomposition of polynomials, not in Mathlib or this library); S10 ergodicity (needs the Poincaré inequality on `S^{n-1}`, proved in the library only for the zonal reductions). `FullTriple.CD` is therefore not instantiated; `sphere_CD` is the pointwise `Γ₂` inequality for the `DiffusionTriple` (`DiffusionTriple.Γ₂`, `ΓA`).
* No theorem identifies `sphereDiffusion 2` with `circleDiffusion` or the zonal `Sphere` through the height function (comparison of the genuine and zonal spheres, plan (c) of R27-J): OPEN.
* No `MarkovProcessBridge`/Feller statement for `S^{n-1}` (needs the semigroup).
* The measure is Mathlib's `toSphere` (cone construction); that it coincides with the Hausdorff/Riemannian measure is not proved (not needed: `ibp_sphere` is the intrinsic characterisation of `L` against `σ`).

## Round 29, Stream Q: `Core2` on the Gegenbauer open-interval family (ERRATA R29-Q-*; `Instances/GegenbauerOpen/Core2/STATEMENTS_R29_Q.md`)
PROVED (axioms `propext, Classical.choice, Quot.sound`; `Core2/Frobenius.lean`, `AxiomCheckR29Q.lean`; 0 warnings, no `sorry`), parametric in real `lam`, `FullTriple`-free:
`Core2Q.gL` (`L_lam = (1-x²)f'' - (2 lam+1) x f'`), `gL_three_halves` (agrees with `goL`), `gL_pow` (`L_lam (1-x)^r = r (1-x)^(r-1) ((r-1)(1+x) + (2 lam+1)x)`), `gL_pow_indicial`, `pow_sq_integrable_iff` (`(1-x)^r ∈ L²((1-x²)^(lam-1/2)dx)` near `x=1` iff `2r+lam+1/2 > 0`), `exponent_regular_L2`, `exponent_half_sub_lam_L2_iff` (`lam < 3/2`), `exponent_three_half_sub_lam_L2_iff` (`lam < 7/2`).
This formalises only the two ingredients of the R26-I exponent count (action of ONE factor `L_lam` on `t^r`; the `L²(ρ_lam)` criterion for `t^r`; the exponent inequalities `lam < 3/2`, `lam < 7/2` are linear arithmetic).  The totals (4, 3, 2 `L²` exponents for `lam < 3/2`, `3/2 <= lam < 7/2`, `lam >= 7/2`), the identification of `0, 1, 1/2-lam, 3/2-lam` as the Frobenius exponents of `(1-L)²u=0` (incl. log resonances) and the Frobenius theory itself are PROSE ONLY, not Lean theorems (R29 Q hostile audit relabel).  NOT `Core2`.
NOT done (precise obstruction): (1) the positive half (`Core2` for some `lam >= 7/2`), (2) the negative half (an explicit deficiency pair for some `3/2 < lam < 7/2`), (3) the threshold theorem.  Reason: every `FullTriple` ingredient (`Basic`, `Diffusion`, `Full/*`, `ESA/*`, `Riemannian/R24/Go*`, about 4000 lines) is hard-wired to `lam = 3/2` (constants `3/4`, `4x`, explicit primitives, the R24 series `aa_n`), so `Core2` for any other `lam` first needs a FullTriple for that weight (PreFull, regularity, semigroup, ESA), and `lam >= 7/2` additionally a fourth-order weak-regularity + Weyl argument.  The `Core2` threshold `7/2` remains the R26-I heuristic, UNPROVED (the R26-I GAPS line above is annotated by this entry, not deleted).  Nothing for `hypRiem` or abstract complete triples.
## Round 29, Stream P: pointwise mass one and the `n = ∞` converse (ERRATA R29-P-*; `Stochastic/R29P/STATEMENTS_R29_P.md`)
PROVED (`Stochastic/R29P/Tight.lean`): for a `C_0`-Feller triple (`IsFellerC0`, `μ` finite on compacts, open positive), `κ_t(x₀, X) = 1` holds iff the Feller kernels are tight near `x₀`
(`fellerKernelInf_univ_eq_one_iff_tight`: for every `ε` there are a compact `K` and a neighbourhood `U` of `x₀` with `κ_t(y, K) ≥ 1 − ε` for μ-a.e. `y ∈ U`; equivalently for every `y ∈ U`, `fellerKernelInf_tight_of_univ_eq_one`);
on a compact space the mass is one everywhere (S11), so a deficit point needs `X` non-compact (`fellerKernelInf_deficit_noncompact`).  So a counterexample to pointwise mass one must lose mass AT INFINITY for starting points converging to `x₀`.
Annotates (does not replace) R25-E-2 / R27-K-1 "OPEN": the question is still neither proved nor refuted; it is now the exact tightness question.  Hand heuristic only (no theorem): 1-D diffusions reduce to `Γ = f'²` in the intrinsic coordinate, where mass loss at a single null point is not expected.
`n = ∞` converse without completeness/Core2 (R24-B-1): STILL OPEN, no counterexample and no proof.  By hand (not formalised): in 1-D `Γ = f'²`, `L = ∂² − V'∂`, `V'' ≥ ρ`, the boundary term has the favourable sign (`V' − ρx` monotone; `V'` bounded at a finite end is a regular end, expected to violate ESA), so 1-D gives no counterexample;
formalised ingredient `oneD_boundary_identity`/`oneD_boundary_bound` (`Stochastic/R29P/OneD.lean`, pure real analysis, not tied to a `FullTriple`).  The abstract route still stops at the `(1−L)𝒜₀` vs `𝒜₀` test-function mismatch (the Core2 gap, ERRATA R15-1).
## Round 29, Stream N: spherical harmonics, `StandardTriple`, conditional `FullTriple` on `S^{n-1}` (ERRATA R29-N-*; `Instances/SphereN/Full/STATEMENTS_R29_N.md`)
Follows BGL §2.2/§2.7. PROVED (axioms `propext, Classical.choice, Quot.sound`, 0 warnings, no `sorry`, `Full/AxiomCheckR29N.lean`; about 750 lines):
* (N2) `fischer` (Fischer decomposition of every homogeneous polynomial into `Σ |x|^{2j} h_j`, `h_j` harmonic homogeneous; purely algebraic in `MvPolynomial (Fin n) ℝ`, by strong induction with `Δ(|x|²q) = (2n+4 deg q)q + |x|²Δq`, so `Δ(|x|^{2j+2}h) = a_j |x|^{2j} h`, `a_j > 0`); `restr_mem` (restrictions of polynomials are in `𝒜₀`); `LS_restr_harm` (`L(h|_S) = −k(k+n−2) h|_S` from `LS_extrinsic` and the Euler identities, for harmonic homogeneous `h` of degree `k`); `restr_mem_span_harm`; `dense_span_harm` (classes of harmonic restrictions span a dense subspace of `L²(σ)`: Stone-Weierstrass for the polynomial subalgebra + Fischer).
* (N3) `sphere_semigroup_harm` (`P_t [h] = e^{−k(k+n−2)t}[h]`); `sphere_esa` = **F10 (ESA) unconditionally**, through the new generic `DiffusionTriple.core_of_dense_range` ((1−L)𝒜₀ dense ⇒ 𝒜₀ is a core; no invariance of 𝒜₀ under `P_t` needed); `sphere_ergodic` = **S10**; `sphere_semigroup_one` and `sphereStandard n hn : StandardTriple (Sph n)` = **S10 + S11 unconditionally**; `sphere_semigroup_poly_mem` (partial F8: for restrictions of polynomials `P_t` stays in `C^∞`).
* (N4) `SphereF8 n hn` (the Prop "`P_t f ∈ C^∞(S^{n-1})` for `f ∈ 𝒜₀`"), `sphereFull hn h8 : FullTriple (Sph n)` with `𝒜 = 𝒜₀ = C^∞(S^{n-1})`, ALL fields proved (F1–F7, F9, F10, S10, S11, using new chain rules `A₀S_comp`, `ΓS_comp_gen`, `LS_comp_gen` for all smooth `ψ`) except F8 = the hypothesis `h8`; `sphereFull_CD : CD (n−2) (n−1)` (from `sphere_CD`); `sphereFull_core2`.
NOT done / obstructions (precise):
* **F8 for all `f ∈ 𝒜₀` is NOT proved**, hence there is NO unconditional `FullTriple (Sph n)`; `sphereFull` is conditional on `SphereF8 n hn`, as `gibbsFull` is on `G.F8`. Exact obstruction: `P_t f = Σ_k e^{−λ_k t} proj_k f`, and smoothness of the sum requires bounds on `C^m` norms of the projections `proj_k f` polynomial (or just subexponential) in `k`. Route identified but not formalised: derivatives of a harmonic homogeneous polynomial are again harmonic homogeneous (so only a sup-norm bound for harmonic polynomials is needed, `‖h‖_∞ ≤ C 2^k ‖h‖_{L²(S)}` from the mean value property on `B(0,2)`, or `C k^{(n−2)/2} ‖h‖_{L²}` from the zonal reproducing kernel), plus `‖∇p‖²_{L²(S)} = k(k+n−2)‖p‖² + k²‖p‖²` from `ibp_sphere`; none of the harmonic mean value property in `ℝ^n`, the zonal kernel, or rotation invariance of `σ` is in Mathlib or this library.
* No Poincaré inequality on all of `L²` (constant `1/(n−1)`), no Obata/Lichnerowicz as inequalities (no orthonormal basis of `L²(σ)` is built; only a dense family of eigenfunctions). The first nonzero eigenvalue is `n−1` (degree 1) by `LS_restr_harm`, but orthogonality of distinct eigenspaces and the Hilbert-basis statement are not proved.
* No Feller/bridge statement for `S^{n−1}`; no comparison with the zonal sphere.


## Round 29, Stream O: closing survey-table entries without a `MarkovProcessBridge` (ERRATA R29-O-*; `Stochastic/R29/STATEMENTS_R29_O.md`)
Annotates the "Round 28, Stream M" survey table (rows annotated, not deleted).  All axioms `propext, Classical.choice, Quot.sound`, 0 warnings, no `sorry` (`R29/AxiomCheckR29O.lean`).
* CLOSED, `lebesgueFull` (1-d Lebesgue `FullTriple` on `ℝ`): `R29.lebesgueFull_bridge : MarkovProcessBridge lebesgueFull.toDiffusionTriple` with kernels `N(x, 2t)` at every `x`.  Route: a direct 1-d port of the R25 argument (`semigroup_cc_aux1`: `P_t u = heatM (√(2t)) f` a.e. for `f ∈ C_c`, by symmetry of Gaussian smoothing + the test-class identification `semigroup_eq_heat`), `lebesgue_isFellerC0`, identification of the R24 Feller kernels with `gaussianReal x (2t)` by weak-Feller uniqueness (`fellerKernelInf_lebesgue`), hence `hM` and `fellerMarkovProcessBridgeInf`; also exact CK `heatKernel1_add` and `heatKernel1_bind` (Lebesgue measure invariant).  No transport between `lebesgueFull` and `lebesgueRdFull 1` was needed.
* CLOSED, open zonal sphere `oStandard`, `oFull` (`(-1,1)`, `S³`, Gegenbauer `λ = 1`, `μO = (2/π)√(1-x²)dx`): `R29.oMarkovProcessBridge`, `oStandard_bridge`, `oFull_bridge`.  The R28-M obstruction (`κ_t(x,{±1}) = 0` for EVERY `x`) is proved: for `t > 0`, `P_t u = Σ_k e^{-k(k+2)t}⟨e_k,u⟩ e_k` has a continuous representative with `‖·‖_∞ ≤ C_t ‖u‖_{L²}`, `C_t = Σ e^{-tk}(k+1)` (`smoothing_sup`; `|U_k| ≤ k+1`), so every compact Feller-kernel mass `κ_t(x,K)` with `μZ(K) = 0` vanishes (Urysohn function supported in a small open set, `sphere_kernel_compact_null`), by inner regularity every `μZ`-null set is `κ_t(x,·)`-null (`sphere_kernel_ac`), in particular the poles (`sphere_kernel_pole_null`; `t = 0` is `κ_0 = δ_x`).  The compact kernels restricted to `(-1,1)` (`Kernel.comapRight`) are Markov kernels with exact CK, `κ_0 = id`, joint measurability, `μO` invariance, and represent `P^O_t` through `PO_restrC` (`KO_rep`, extension by zero).  Note: the bound is a Hilbert-Schmidt-type estimate specific to the Gegenbauer spectrum (`|U_k| ≤ k+1`); no boundary-behaviour (Feller entrance/polarity) argument is used.
* PARTIAL, `gaussRdFull d`: the product Mehler kernels `mehlerKernelRd d t = N(e^{-t}x, (1-e^{-2t}) I_d) = ⊗ ouKernel t (x_i)` are proved Markov, jointly measurable, with `κ_0 = id`, exact Chapman-Kolmogorov (`mehlerKernelRd_add`) and `N(0,I_d)` invariant (`mehlerKernelRd_bind`).  The bridge itself is only CONDITIONAL: `gaussRdFull_bridge_of_rep` needs (i) `(gaussRdFull d).μ = gam d` (the normalised Gibbs density `Z⁻¹e^{-|x|²/2}` identified with the product Gaussian: not in the library, `GaussFinite.lean` says "informally") and (ii) `IsTestClassRep` (Mehler formula for the Friedrichs semigroup of `gaussRdFull d` on `C_c^∞(ℝ^d)`).  For (ii) the 1-d proof uses Hermite completeness (`Pt_mehler`); a `d`-dim route would be (α) Gaussian IBP + `∂_t M_tψ = L M_tψ` pointwise, (β) `M_tψ ∈ 𝒟(L)` by `mem_domain_of_Γ₂` (`gaussRdFull_CD`, `gaussRdFull_core2`), (γ) the Duhamel argument of `LebesgueRd/Full/Identify.lean` with the Mehler flow in place of the heat flow, which needs the `L²`-differentiability of `t ↦ [M_tψ]` (the analogue of `HeatDerivAux1-5`, several hundred lines); alternatively the generator-at-`0` + essential self-adjointness route (`esa` field + abstract uniqueness of the semigroup with given generator, no such lemma in the library).  Neither route is attempted here.
* NOT closed, Gibbs/elliptic/Riemannian (`gibbsFull_unconditional`, `gibbsRdFull_unconditional`, `fullU`, `riemFull_unconditional`; `gibbsStandard_*` are the same semigroups): the topological hypotheses of the R24/R27 theory HOLD (reference measure a probability measure with full support: instances `R29.gibbsFull_locFin/_openPos`, `gibbsRdFull_*`, `fullU_*`, `riemFull_*`), but three hypotheses are missing: (a) `IsFellerC0` (`P_t C_c ⊂ C_0`: for non-Gaussian `V` or non-constant elliptic data there is no Mehler/heat formula; only the Gaussian and Lebesgue cases have kernel formulas), (c) `κ_s(x,·) ≪ μ` at EVERY `x` (only `μ`-a.e. `x` follows from the `L²` representation), (d) the pointwise initial condition `Q_t f(x) → f(x)` as `t ↓ 0` for `f ∈ C_c`.  Delivered conditional bridges `gibbsFull_bridge_of_feller`, `gibbsRdFull_bridge_of_feller`, `fullU_bridge_of_feller`, `riemFull_bridge_of_feller` (the R27 theorem `fellerMarkovProcessBridgeInf_of_ac_init` instantiated).  For the Gaussian `ℝ^d` case (c), (d) would follow from the explicit Mehler kernels once (ii) above is available.
* `trivialCompact`: unchanged (degenerate sanity triple, nothing to gain).
