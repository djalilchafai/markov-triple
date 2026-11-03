# Self-audit, round 15 "Interp" stage (StrongInterpolation for every FullTriple)

Targets fixed beforehand: `Theory/Interp/STATEMENTS_R15_Interp.md` (T1 main, T2 consequence, T3 `ibp_bdd`, T4 analytic lemmas).
Everything below is an attack by the author on his own statements; an independent hostile audit is still to be done.

## 1. What was proved (all `#print axioms` = propext, Classical.choice, Quot.sound; see `Theory/Interp/AxiomCheck.lean`)
| Book | Lean (file) |
|---|---|
| Lemma 3.3.20 (p. 163) | `FullTriple.lemma3320` (`Lemma3320`): `G_ε = ψ_ε(Γ g) ∈ L²`, `[G_ε] ∈ 𝒟(ℰ)`; plus `integrable_L_psi`: `L G_ε ∈ L¹` |
| Lemma 3.3.21 "by density" (p. 164) | `FullTriple.ibp_bdd` (`IbpBdd`): `∫Γ(G,k) = -∫ k L G` for bounded `k ∈ 𝒜 ∩ 𝒟(ℰ)`, `L G ∈ L¹` |
| "∂_s Φ is then justified" (p. 164) | `hasDerivAt_integral_comp`, `hasDerivAt_pair`, `continuous_pair` (`Nemytskii`, `Pairing`) |
| `∂_s Γ(P_{t-s} f)` | `FullTriple.hasDerivAt_cK` (form-norm differentiability of `s ↦ P_s f`), `hasDerivAt_uK` (`L¹`-derivative `2Γ(P_s f, P_s Lf)`) (`Orbit`, `Curve`) |
| Thm 3.3.18 interpolation | `FullTriple.strongInterpolation : T.CD ρ n → T.StrongInterpolation` (`StrongMain`), any `FullTriple` |
| Thm 3.3.18 | `FullTriple.strong_gradient_bound_unconditional` (`Main`) (`ρ ≥ 0`) |
| Gibbs, OU | `GibbsData.gibbsFull_strong_gradient_bound_unconditional` (`Instances/Gibbs/InterpMain`), `ouFull_strongInterpolation_generic`, `ouFull_strong_gradient_bound_generic` (`Instances/OU/InterpGeneric`) |

## 2. Attacks on the statements
* **Frozen structures unchanged.**  `strongInterpolation` has type exactly `T.StrongInterpolation` (frozen `Strong/Main.lean`, not edited);
  `python3 scripts/check_frozen.py` prints OK; only `MarkovTriple.lean` (import list) and new files were touched.
* **Vacuity / junk values.**  `StrongInterpolation` contains the integrability conjuncts, and they are proved (`iA`, `iD` in `StrongMain`),
  so the Bochner integrals in `HasDerivAt` are not junk `0`.  The derivative value is the frozen `∫ P_s h · strongD ε g_s`, and
  `strongD` involves `T.L (psiS ε ∘ Γ g)` (the `𝒜`-operator `L`), which is identified with the closed form by `lemma3320`, `ibp_of_domain`, `ibp_bdd`.
* **a.e. vs everywhere.**  `Pt` is a *choice* of `𝒜`-representative; all identifications (`strongPhi_eq`, `ucurve_ae`, `L_Pt_ae`) are a.e.; the integrals
  are insensitive.  `L` on `𝒜` is a total function whose a.e.-class depends only on the a.e.-class (ALevel): used only through `generator_ae_L`.
* **Endpoints.**  `t = 0`: `Ioo 0 0 = ∅` (derivative clause vacuous), continuity on `Icc 0 0` trivial.  For `t > 0` the continuity on `[0,t]`
  (including `s = 0` and `s = t` where `P_{t-s}` degenerates) is proved for ALL `r ∈ ℝ` (`continuous_pair`: inner product of two continuous
  `L²` curves; `r ↦ ψ(u_r)` is `L²`-continuous from `‖ψ(u)-ψ(v)‖₂² ≤ ‖u-v‖₁`), so no one-sided derivative is used.
* **`ρ < 0`.**  `strongInterpolation` is proved for every `ρ ∈ ℝ` (CD only enters through `Γ₂ ∈ L¹`, `Γ(G_ε) ≤ Γ₂ - ρΓ`, `|ψ''|Γ(u) ≤ (Γ₂-ρΓ)/ε`).
  The *consequence* `strong_gradient_bound_unconditional` needs `ρ ≥ 0` (frozen `strong_eps`); not extended.
* **The hypothesis `h ≥ 0`** of `StrongInterpolation` is not used (the derivative formula holds for any `h ∈ 𝒜₀`).
* **Boundedness.**  `P_s h` bounded uses D2 (`𝒜₀` is bounded everywhere) and the sub-Markov property `ae_abs_semigroup_le` (copy of the compact-case lemma for a
  general `DiffusionTriple`).  The book writes "since `P_t h` is bounded"; same.
* **Where F-axioms are used.**  F7 only for `χ(a_j) ∈ 𝒜₀` in `ibp_bdd` and through `ibp_of_domain`; F3 for `χ∘a_j ∈ 𝒜₀` and `ψ_ε∘Γ g ∈ 𝒜`; F6 `ΓA_comp_left/_comp`;
  F8 (via `Pt`), F10 (ESA) only through `mem_formDomain_of_ESA`, `generator_ae_L`, `integrable_Γ₂_of_domain`.  The converse of Prop. 3.3.17 is NOT used.

## 3. Deviations from the book (candid)
1. The book prints `√(r+ε²) − ε ≤ √r` (Lemma 3.3.20, p. 163; the `√` on the right was lost in plain-text extraction, so an earlier version of this note wrongly called the book's bound false: audit R15-Interp finding 1).  We use its squared form `(√(r+ε²) − ε)² ≤ r` (`psiS_hH`), so `‖G_ε‖₂² ≤ ∫Γ`.
2. "Derivation of `Φ` is then justified" (the book differentiates `Φ(s) = ∫ h P_s G_ε` under the integral using `‖∂_sG_ε‖₁ + ‖∂²_sG_ε‖₁ ≤ C`): a pointwise-in-`s`
   argument is unavailable (`P_s h`, `Γ(P_{t-s}f)` are only classes, no joint regularity).  We differentiate in `L¹`/`L²`: `s ↦ Γ(P_s f)` is `L¹`-differentiable
   (`GB`, bounded bilinear on the form space `K`), `ψ_ε∘` is `L¹`-differentiable by a uniform-integrability estimate (`remainder_integral_le`), product rule `hasDerivAt_pair`.
3. Lemma 3.3.21 "extended to any bounded `h ∈ 𝒟(ℰ)` by density" needs a truncation: done in `ibp_bdd` (the functional `h ↦ ∫ h LG` is not form-continuous since `LG ∈ L¹` only).
4. The book proves `∂_s G_ε`'s sign pointwise; here the identification of the derivative with `∫ k·strongD` is exact (equality), and the sign is the already-frozen `strongD_ge`.
5. G1 (`GradientInterpolation`, equality `Φ' = 2∫P_sh Γ₂`) is NOT a book statement and is not proved (see `GAPS.md` Round 15 Interp).

## 4. Not done (exact)
* **Weak form Cor. 3.3.19 for non-compact triples** `Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)`: the book obtains it from Thm 3.3.18 "by Jensen's inequality for `P_t`, sub-Markov".  Missing in the library:
  `(P_t w)² ≤ P_t(w²)` a.e. for `0 ≤ w ∈ L² ∩ L^∞` (positivity + `P_t u ≤ 1` for `u ≤ 1`; for infinite `μ` it needs `(w - λ u_c)²` with `u_c = w/(w+c) ∈ L²`, then `c → 0`).
  Not attempted for lack of capacity; it is an `L²`-operator lemma independent of the triple.
* **G3 `EntropyInterpolation`, G3' `FiniteDimInterpolation`**: not attempted.  Analysis: `I(s) = ∫Γ(g_s)/g_s` is `∫ u_s θ(g_s)` with `u_s ∈ L¹`-differentiable and `θ(g_s) = 1/g_s`
  bounded, only `L²`-differentiable; the analogue of `hasDerivAt_pair` needs `θ(g_r) → θ(g_s)` in measure plus uniform integrability of `Δu/δ` (same technique as `remainder_integral_le`), and
  `I' = -2J` needs `L(g Γ(Λ g))`-type integrations by parts (Prop. 3.3.17 forward).  No missing book lemma was identified, but it is a second, comparable development.
* `ρ < 0` of Thm 3.3.18 (error term, GAPS).

## 5. Attack surface for the independent audit
1. `hasDerivAt_integral_comp`: the hypotheses `hrem`, `hψ'`, `hH` are stated on `[0,∞)` only, and `u ≥ 0` a.e. is needed at every `r`; check `psiS_rem` (`PsiBounds`) really gives
   `|R| ≤ |b-a| min(K₂|b-a|, 2K₁)` with `K₁ = 1/(2ε)`, `K₂ = 1/(8ε³)` (proved, but the constants are easy to get wrong).
2. `GB`/`GBl`: bilinear `K × K → L¹` obtained from `gammaE_lin_left/right`; the `erw`/`rfl` steps close `Q` vs `T.formDomain` defeq mismatches; check `GB_apply`.
3. `hasDerivAt_cK` / `norm_cK_le`: the bound `‖v‖_K ≤ ‖v‖₂ + ‖Lv‖₂` (from `kn_sq`: `‖v‖_K² = ℰ(v) + ‖v‖²`) and the use of subtype arithmetic in `↥generator.domain`.
4. `ibp_bdd`: truncation `chiT (|M|+1)` equals the identity on `[-(|M|+1), |M|+1]`; `deriv χ (k x) = 1` a.e.; subsequence bookkeeping (`φ`, `hbk`); F7 used for `χ ∘ a_{φ n} ∈ 𝒜₀`.
5. `strongInterpolation`: the three identifications `eA`, `eB`, `hu'` (sign `-2Γ(g,Lg)` and `ucurve f t r = Γ(P_{t-r}f)` with the reparametrisation `r ↦ t - r`, `HasDerivAt.comp_const_sub`).
6. `lemma3320`: `Γ(G_ε) ≤ Γ₂ - ρΓ` uses `reinforced_cd` (3.3.6, proved in round 12) and `ΓA_comp_comp`; `integrable_L_psi` needs `L g ∈ 𝒟(ℰ)` (true for `g = P_τ f`, `f ∈ 𝒜₀`) — an extra hypothesis of the lemma, discharged in `StrongMain` by `toLp_L_Pt`.
7. Whether a *hidden* use of compactness or of `ρ ≥ 0` exists in the new files (none intended; `ρ ≥ 0` only in `Main.lean`).
