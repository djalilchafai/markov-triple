# Round 15 self-audit: regularity of the Gibbs triple (`GibbsData.weakHypo`, `GibbsData.f8`)

Scope: `Instances/Gibbs/Reg{Analysis,Core,Bridge,Hypo,Semigroup,Main}.lean`; target statements frozen in
`Instances/Gibbs/STATEMENTS_R15_Reg.md` (no erratum was needed: the proved statements R0-R4 are the stated ones;
extra helper lemmas only).  The definitions `GibbsData.WeakHypo`, `GibbsData.F8` (FunctAlgebra.lean) are textually
unchanged (only docstrings point to the new theorems).

## Attacks on the statements, and findings

1. **F8 vacuous via a.e. freedom?**  F8 asks for `g ∈ Afull = {f | ContDiff ℝ ⊤ f}` with
   `P_t[f] =ᵐ[μ] g`.  Any class has many a.e.-representatives, but a smooth one is UNIQUE since `μ` has full
   support: `afull_rep_unique` (two smooth `μ`-a.e. equal functions are equal).  So the statement says exactly that
   the class has a smooth version; it is not trivially true (a generic `L²` class has none).
2. **F8 trivial for `t = 0`?**  Yes, `P_0 = id` (`semigroup_zero`), only `f ∈ 𝒜₀ ⊂ 𝒜`; the content is `t > 0`.
3. **WeakHypo quantifiers.**  `∀ λ ∈ ℝ, ∀ f ∈ L²(μ)`, hypothesis tested on every `a ∈ 𝒜₀ = C_c^∞` (subtype
   `G.gibbsDiff.A₀`): `∫ f L a dμ = ∫ (λ f) a dμ`.  Conclusion `∃ g ∈ 𝒜, f =ᵐ g`.  Matches BGL Def. 3.3.8 / Def. 3.1.9
   (`L*f = λ f`).  Non-vacuity of the premise: `weakHypo_premise_satisfiable` (constant class `1`, `λ = 0`).
4. **Junk values.**  `GibbsData` carries no `V'' ≥ ρ`, no `ρ > 0`: both theorems are proved for every smooth `V` with
   `e^{-V}` integrable (regularity is local; the semigroup argument is abstract).  No `rcfc` junk value is used:
   the only use is through `Hilbert.cfcSemigroup_eq_pow_mul` (an identity of operators) and `R^{m+1}` applied to the
   vector `ψ(R) f`, whatever that is.  `deriv`/`Lg` junk: all functions are smooth on the relevant classes.
5. **a.e. conventions.**  Core regularity is proved for Lebesgue-a.e. representatives; converted to `μ`-a.e. by
   `ae_mu_of_ae_vol` (`μ = volume.withDensity (ofReal ∘ w) ≪ volume`).  Integrability transfer
   `integrable_w_mul` uses `integrable_withDensity_iff_integrable_smul'` (uses `w > 0` only through `toReal_ofReal`).
6. **Representatives for different `n` agree.**  `smooth_rep_of_forall`: for each `n` a `C^n` representative exists;
   all agree everywhere with the `n = 0` one (continuous + volume-a.e. equal), so that single function is `C^∞`.
7. **Is the resolvent identity genuinely the weak equation of the *Friedrichs* operator?**  It is the library's
   frozen `FormData.R_resolvent` (`R(f + A f) = f` on `D`, `A[f] = -[L f]` by `formA_apply`) plus self-adjointness of `R`;
   `DiffusionTriple.resolvent_weak` derives `∫ (Rv) L a = ∫ (Rv - v) a` from these only.
8. **Smoothing step.**  `P_t = R^k ψ_{t,k}(R)` for `t ≠ 0` is the library theorem `cfcSemigroup_eq_pow_mul`
   (frozen file), `DiffusionTriple.semigroup t = cfcSemigroup R t` by definition (`formData.semigroup`).

## Math route (what was formalised)
* `RegAnalysis`: antiderivative of a zero-mean `C_c^∞` function, du Bois-Reymond, AC integration by parts
  (`AbsolutelyContinuousOnInterval` + Lebesgue differentiation from Mathlib), compactly supported product rule.
* `RegCore`: `w L a = (w a')'`; weak form `∫ u (w a')' = -∫ H a'` with `H = ∫₀ˣ w h`; adding a multiple of a fixed bump
  gives all test functions; `b = φ/w` yields `u' = (H - c0)/w` distributionally, continuous; du Bois-Reymond gives
  `u = ∫ v + c`, `C¹`; bootstrap `h ∈ C^j ⇒ u ∈ C^{j+2}`.
* `RegHypo`: `h = λ u`, induction `u ∈ C^n ⇒ u ∈ C^{n+1}`.
* `RegSemigroup`: `x = R v` solves `L x = x - v` weakly; `v ∈ C^j ⇒ x ∈ C^{j+2}` (inner induction on the exponent);
  `R^{m+1} g ∈ C^{2m+1}`; with the smoothing identity, `P_t f ∈ ∩_n C^n`.

## Residual risks / where a hostile auditor should look
* Casts `ℕ → WithTop ℕ∞` (`exact_mod_cast`): compiled, but check `ContDiff ℝ ((j:WithTop ℕ∞)+2)` is what is meant.
* `Sm f := ContDiff ℝ (⊤ : ℕ∞) f` is `C^∞`, not analytic (`ω`).
* `weak_vol` identifies `∫ F dμ` with `∫ w F dx` (existing `integral_μ`).
* `resolvent_weak` is stated for a general `DiffusionTriple`; check `S.emb`/`opA` unfolding (proved by `rfl` + `formA_apply`).
* `gibbsFull_logSobolev` / `gibbsFull_gradient_bound` remain conditional on `EntropyInterpolation` /
  `GradientInterpolation` (open item (c) of GAPS, unrelated to this round).
