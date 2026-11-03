# Self-audit, round 16 (Jensen stage)

Candid process note: `STATEMENTS_R16_Jensen.md` was written with the plan fixed, but the file was committed to disk after the first
compiling draft of `Jensen.lean` (statements unchanged between plan and proof; the hypotheses of `jensen_sq` are those of the plan).

## Attacks on my own statements
1. **Vacuity of `jensen_sq`.**  Hypotheses `hpos`, `hle` are discharged for the real operator `semigroup t` by the existing theorems
   `semigroup_nonneg`, `semigroup_le_one` (not assumed).  For `P = 0` or `P = id` the statement is true/trivially consistent; no contradictory hypotheses.
2. **Class of `w`.**  Proved: `0 ≤ w ∈ L²`, `W = w²` a.e. (so `w ∈ L⁴` implicitly, since `W ∈ L²`).  Used: `w = sqrtΓcls f` with `W = [Γ f]`, `Γ f ∈ 𝒜₀ ⊂ L²`
   (`hW` in `JensenGrad.lean` is proved, not assumed).  Exact match; no bounded-`w` restriction, no density/monotone-limit step is hidden.
3. **a.e. conventions.**  All statements are a.e. for chosen `Lp` representatives (`coeFn`); `jensen_sq` gives `(P w x)² ≤ P W x` for a.e. x for the
   canonical representatives; `P W` is `semigroup t (cls ⟨ΓA f f, _⟩)` literally the RHS class of `HasGradientBound` / `gradient_bound`.
4. **Infinite μ.**  Constants never appear in `L²`: truncations `u_n = min(1, n w) ≤ n w ∈ L²`; `P(u_n²) ≤ 1` by the sub-Markov property applied to `u_n² ≤ 1`
   (no `P 1` needed).  Convergence `w u_n → w` in `L²` by dominated convergence with dominant `w² ∈ L¹`.
5. **Junk for non-`L²` functions.**  None: `T.Pt t f` is a representative in `𝒜` of the class `P_t f` (`Pt_ae`); `ΓA` of it is compared via `Pt_mem_A`
   and `ΓA_nonneg` (a field of `FullTriple`).  `HasGradientBound` is discharged with the same `ΓA_congr_A`/`cls` bookkeeping as the existing `FullTriple.hasGradientBound`.
6. **`ρ ≥ 0` only.**  `gradient_bound_unconditional` needs `strong_gradient_bound_unconditional`, which needs `ρ ≥ 0` (not merely a sign convention of mine: the eps-form
   with `ρ < 0` has an uncontrolled error term, `GAPS.md`).  Hence `HasGradientBound ρ` is discharged for `ρ ≥ 0` only; `ρ < 0` is open.  Note `CD(ρ,n)` with `ρ>0`
   needs no extra care: weak bound `e^{-2ρt}` is what is proved.
7. **Squaring step.**  `√G ≤ e^{-ρt} Pw` with `G ≥ 0` gives `G ≤ (e^{-ρt}Pw)²` (monotone `x ↦ x²` on `[0,∞)` via `gcongr`, needing `0 ≤ √G`; the RHS need not be known nonneg a priori:
   `0 ≤ √G ≤ RHS` makes it so).
8. **Frozen definitions** `GradientInterpolation`, `HasGradientBound`, `FullTriple` untouched.  `GradientInterpolation` itself is NOT proved (not a book statement); the old
   conditional theorems (`gibbsFull_gradient_bound`, `FullTriple.hasGradientBound`, OU/Lebesgue ones) are unchanged.

## Not done (exact)
* `ρ < 0` (weak and strong).  * `GradientInterpolation` (G1).  * `EntropyInterpolation` (G3), `FiniteDimInterpolation` (G3').
* Mass conservation for Gibbs/GibbsRd: the generic `conservative_of_complete_unconditional` applies (needs `IsComplete`, available `gibbsDiff_isComplete`),
  but a Gibbs instance line was not added (finite measure; conservativeness there is already known).

## Attack surface (for the hostile auditor)
1. `jensen_sq`: the `ae_all_iff` over `ℚ`, the identity `P Z = P W − 2q P B + q² P S` and `Lp.coeFn_*` rewriting chain; the claim `Z =ᵐ (w − q u_n)²` (`hZ0`).
2. `sq_le_of_forall_rat` (density of `ℚ`; constants `δ`).
3. `hconv`: `‖B n − w‖² = ∫ (w(u_n − 1))²` via `L2.inner_def`; the pointwise limit (eventually `u_n = 1`, or `w = 0`); `exists_nat_ge (1/w)`.
4. `gradient_bound_unconditional`: `hW` (class `[Γ f]` equals `(sqrtΓcls f)²` a.e.) — check `ΓA f.1 f.1` is the `Γ f` of `Γ f ∈ 𝒜₀` used in `HasGradientBound`.
5. `hasGradientBound_unconditional` copies `FullTriple.hasGradientBound`; verify `e2` (class of `c`) and `e1` (`ΓA` of arbitrary `𝒜`-representative `g`).
6. `semigroup_nonneg`/`semigroup_le_one` hypotheses in the `L²` form (`u ≤ 1` as functions with `(1 : E → ℝ)`); `Lp` coercion mismatch is not a problem (it type-checks).
7. Whether `strong_gradient_bound_unconditional` (round 15, previous agent) is itself sound: this stage inherits it entirely.
