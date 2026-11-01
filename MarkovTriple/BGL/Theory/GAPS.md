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
**Not done:** the *strong* (√) form `Γ(P_tf) ≤ e^{-2ρt}(P_t√Γf)²` (Thm 3.3.18): needs in addition the
pointwise inequality (3.2.4)/(3.3.7) `Γ(Γ f) ≤ 4(Γ₂(f)-ρΓ(f))Γ(f)` on `𝒜` (the `ψ(h)`-trick
of the book on p. 159, a Hessian computation) and the second derivative `∂²_s G_ε` of Lemma 3.3.21 with
the `ε`-regularisation `G_ε = √(Γ+ε²)-ε`.  The weak form is what mass conservation and Poincaré-type
applications use.

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

* **G4.  Mass conservation, infinite `μ` (Thm 3.3.23).**  Finite `μ`: done and stronger (ESA alone).  For infinite `μ`
  the book needs *completeness* (Def. 3.3.9: `ζ_k ↑ 1` in `𝒜₀`, `Γ(ζ_k) ≤ 1/k`), which is NOT a field of the surface,
  plus the gradient bound (G1).  Sketch (not formalised): `∫(P_tζ_k-ζ_k)ξ = -∫_0^t∫Γ(P_sζ_k,ξ)`, Cauchy–Schwarz
  and `Γ(P_sζ_k) ≤ e^{-2ρs}P_sΓ(ζ_k) ≤ e^{-2ρs}/k` give `→ 0`; in infinite measure one needs `√Γ(ξ) ∈ L¹`, available
  for `ξ = η²`, `η ∈ 𝒜₀`, which suffices by density.  Second claim of Thm 3.3.23 (`ρ>0 ⇒ μ(E)<∞`) likewise not done.
  Without completeness the statement "ESA + CD ⇒ conservative" is not claimed (the book assumes completeness).
* **G5.  Props. 3.3.16 (i),(iii)–(viii) and 3.3.17 as operator statements** (extension of `Γ₂`, Hessian to `𝒟(L)`
  as `L¹`-valued continuous bilinear maps; identification on `𝒜 ∩ 𝒟(L)`; converse under ergodicity).  Only the
  integrated identities / inequalities (which suffice for Poincaré) are proved.
  Note Remark 3.3.15 (CD from `𝒜₀` to `𝒜`) is not needed: the frozen `FullTriple.CD` is already stated on all of `𝒜`.
* `FullTriple.CD` for the finite-dimensional LSI constant `ρn/(n-1)` (Thm 5.7.4 with `n<∞`, via the integrated
  chain rule (5.7.6)–(5.7.12) for `e^{ag}`): not done (only `n`-independent constant `1/ρ`, from `CD(ρ,n) ⇒ CD(ρ,∞)`).
