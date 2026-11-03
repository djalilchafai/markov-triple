# STATEMENTS R15 (Armstrong method): regularity for the Gibbs triple — written BEFORE the proofs

Goal: prove, for every `G : GibbsData` (smooth `V`, `e^{-V}` integrable; in particular for `V'' ≥ ρ > 0`),
the two hypotheses of `FunctAlgebra.lean`, with **unchanged definitions** `GibbsData.WeakHypo` (BGL Def. 3.3.8
with `𝒜 = C^∞(ℝ)`, all `λ ∈ ℝ`) and `GibbsData.F8` (BGL Def. 3.3.1 (viii): the L²-class `P_t[f]`, `f ∈ 𝒜₀`,
`t ≥ 0`, has a representative in `C^∞(ℝ)`; `P_t` = frozen `DiffusionTriple.semigroup`, the Friedrichs semigroup).

Classical theorems formalised (BGL cites them unproved: Sect. 1.12 pp. 49-50, p. 157):
* (E) 1-D elliptic regularity of the weighted Sturm–Liouville operator `L f = f'' - V' f' = w⁻¹ (w f')'`,
  `w = e^{-V}/Z`: a locally integrable weak solution of `L u = h` is `C¹`, with `w u' = c + ∫₀ˣ w h`
  (du Bois-Reymond lemma + integration by parts for absolutely continuous functions); and `h ∈ C^j ⇒ u ∈ C^{j+2}`.
* (S) Smoothing of the Friedrichs semigroup / analytic-semigroup range property: for `t > 0`,
  `P_t = R^k ψ_{t,k}(R)` (`Hilbert.cfcSemigroup_eq_pow_mul`, `R = (1-L)⁻¹` the Friedrichs resolvent), so
  `P_t f ∈ Ran R^k` for every `k` (`⊂ 𝒟(L^k)`); weakly `∫ (R v) L a = ∫ (R v - v) a` for `a ∈ C_c^∞`, and (E) iterated.

## Statements (namespace `MarkovTriple.BGL.Instances.Gibbs`, `GibbsData`)

R0 (core, `RegCore.lean`; w = `G.w`).  For `u h : ℝ → ℝ` with `w·u`, `w·h` integrable on `ℝ` (volume) and
`∀ a, Sm a → HasCompactSupport a → ∫ w·(u·Lg V a) = ∫ w·(h·a)`:
`∃ U c, ContDiff ℝ 1 U ∧ u =ᵐ[volume] U ∧ ∀ x, w x * deriv U x = c + ∫ y in 0..x, w y * h y`.
R1 (`RegCore.lean`). If moreover `h =ᵐ h̃` with `ContDiff ℝ j h̃` (`j : ℕ`) then `U` can be taken `ContDiff ℝ (j+2)`.

R2 (`RegHypo.lean`).  `theorem GibbsData.weakHypo (G : GibbsData) : G.WeakHypo`.
R3 (`RegSemigroup.lean`).  `theorem GibbsData.f8 (G : GibbsData) : G.F8`.

R4 (`RegMain.lean`, unconditional corollaries; old names/signatures untouched):
`gibbsStandard_unconditional`, `gibbsFull_unconditional : FullTriple ℝ`, `gibbsFull_CD_unconditional`,
`gibbsFull_poincare_unconditional`, `gibbs_poincare_unconditional` (`G.gibbsDiff.PI (1/ρ)` for `0<ρ`, `V''≥ρ`),
`gibbs_spectralGap_unconditional`, `gibbs_expDecay_unconditional`, `gibbsDiff_esaProp_unconditional`,
`gibbsDiff_ergodic_unconditional`, defined/proved as the old ones applied to `G.weakHypo`, `G.f8`.

## Notes for the attack (self-audit anticipations, see AUDIT_R15_REG_SELF.md)
* `F8` and `WeakHypo` are statements about a.e.-classes, with representative required in `𝒜` (everywhere smooth).
  Since `μ` has full support (w > 0, continuous) two continuous representatives coincide everywhere, so the
  representative is unique: the statement is not vacuous (a.e. freedom does not trivialise it).
* `WeakHypo` is hypothesis-free about `V''`; it is true for any smooth `V` (local regularity).
* `F8` at `t = 0`: `P_0 = id`, trivially smooth.  For `t > 0` it is a real statement.
