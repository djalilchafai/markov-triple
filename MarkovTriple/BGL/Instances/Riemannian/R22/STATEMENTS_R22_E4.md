# Round 22, Stream E4 (Riemannian / non-compact CD): statements fixed BEFORE the proofs

Method: statements first; any change is logged in `## Status` and proposed as an `ERRATA.md` row prefixed `R22-E4-`.
Namespaces: `MarkovTriple.BGL.Lebesgue` (part N), `MarkovTriple.BGL.Instances.Riemannian` (part H).
Files: `R22/NonCompactCD.lean` (N), `R22/HypCutObstruction.lean` (H), `R22/AxiomCheckR22E4.lean`.

## Background facts found in the repository (not new)
* `Lebesgue/Full.lean`: `lebesgueFull : FullTriple ℝ` (`𝒜₀ = C_c^∞(ℝ)`, `𝒜 = C^∞(ℝ)`, `L f = f''`, `μ` = Lebesgue measure, infinite),
  `lebesgue_CD : ρ ≤ 0 → 1 ≤ n → lebesgueFull.CD ρ n`.  So a genuinely non-compact finite-`n` `FullTriple` with `CD` already exists in dimension 1
  (ERRATA R17-M2 concerned `SphereOpen`, not `lebesgueFull`).
* `Riemannian/Core2RiemMain.lean`: `RiemData.riem_core2 : R.Curv ρ → R.toEll.CoreCut → Core2`; `Core2EllRadial*`: `RadialJets → CoreCut`.
* `AUDIT_R19_CORE2ELL.md` §6 (by hand, not formalised): `hypRiem.toEll` has no `CutFamily` (so `CoreCut` fails).

## Targets

### Part N (iii): non-compact finite-`n` CD, what the library contains, with sharpness
```lean
namespace MarkovTriple.BGL.Lebesgue
-- N1 exact characterisation of CD for the Brownian full triple on ℝ
theorem lebesgue_CD_iff {ρ : ℝ} {n : ℝ≥0∞} : lebesgueFull.CD ρ n ↔ ρ ≤ 0 ∧ 1 ≤ n
-- N2 the instance is genuinely non-compact with 𝒜 ≠ 𝒜₀ (as sets of functions) and infinite μ
theorem lebesgueFull_noncompact : NoncompactSpace ℝ ∧ lebesgueFull.μ Set.univ = ⊤
theorem lebesgueFull_A_ne_A₀ : (lebesgueFull.A₀ : Set (ℝ → ℝ)) ≠ lebesgueFull.A   -- 1 ∈ 𝒜 \ 𝒜₀
-- N3 for ρ ≤ 0 and every n ∈ [1,∞]: CD(ρ,n) holds (`lebesgue_CD`); in particular CD(0,1) and CD(0,∞).
```
Not claimed: any `FullTriple` on `ℝ^d`, `d ≥ 2` (see Status).

### Part H (i): `Core2`/`CoreCut` for `hypRiem`
Goal as assigned: `hypRiem.toEll.CoreCut` or a `RadialJets` criterion.  By AUDIT_R19 §6 this is FALSE (no `CutFamily`), so the Lean targets are the
formal obstruction to the `RadialJets` route, with `V = 2cosh d`, `ψ = log(1+V)`:
```lean
namespace MarkovTriple.BGL.Instances.Riemannian
-- H1 radial jets of V:   L V = -V² + 2V + 4,  Γ(V) = V² - 4
theorem hyp_L_V (z : Rd 2) : hypRiem.toEll.L Hyp.V z = -(Hyp.V z) ^ 2 + 2 * Hyp.V z + 4
theorem hyp_Γ_V (z : Rd 2) : hypRiem.toEll.Γ Hyp.V Hyp.V z = Hyp.V z ^ 2 - 4
-- H2 the radial-growth hypothesis of `RadialJets` fails for the two natural exhaustions
theorem hyp_not_radialJets_V (α β : ℝ → ℝ) : ¬ RadialJets hypRiem.toEll Hyp.V α β
theorem hyp_not_radialJets_psi (α β : ℝ → ℝ) : ¬ RadialJets hypRiem.toEll Hyp.psi α β
-- H3 quantitative form: no `C` with |Lψ| ≤ C(1+ψ)
theorem hyp_L_psi_unbounded : ¬ ∃ C : ℝ, ∀ z, |hypRiem.toEll.L Hyp.psi z| ≤ C * (1 + Hyp.psi z)
```
NOT targeted (out of reach, see Status): `hypRiem.toEll.CoreCut`, `Core2` for `hypRiem`, a formal proof that no `CutFamily` exists.

### Part A (ii): atlas / two-chart
Assessment only (Status).  No Lean target.

## DIFFERENCE FROM BGL
* BGL does not treat `CoreCut`/`Core2` (R15-1); `CutFamily` is this library's graph-norm cut-off hypothesis with bounds on `Γχ, Lχ, L²χ, Γ(Lχ), Γ₂χ`.
* `lebesgueFull` has infinite `μ`; BGL's Standard Markov Triple allows this (S10 means `u = 0`, S11 through exhaustion sequences, see `StandardTriple`).
* `FullTriple.CD` includes the conjunct `1 ≤ n` (as in the book); `lebesgue_CD_iff` is therefore not a statement about `n < 1`.

## Status
All targets N1, N2, N3, H1, H2, H3 PROVED as stated (statement section unchanged).  Names as proved:
`MarkovTriple.BGL.Lebesgue.{lebesgue_CD_iff, lebesgueFull_noncompact, lebesgueFull_A_ne_A₀}` (file `NonCompactCD.lean`);
`MarkovTriple.BGL.Instances.Riemannian.hypRiem.{hyp_L_V, hyp_Γ_V, hyp_L_V_unbounded, hyp_L_psi_unbounded, hyp_not_radialJets_V,
hyp_not_radialJets_psi}` (file `HypCutObstruction.lean`; the theorems live in the namespace `hypRiem`, i.e. `hypRiem.hyp_L_V`, not at top level;
helpers `wg_eq, Γ_V_eq, inner0, inner1, Δg_V, pt, V_pt, L_psi, L_psi_le`).  `AxiomCheckR22E4.lean`: only propext, Classical.choice, Quot.sound.
Deviation: H3 is stated for `V` as well as for `ψ` (`hyp_L_V_unbounded`).  No sorry, no set_option, no warnings.

### (i) `CoreCut`/`Core2` for `hypRiem`: NOT achieved, and cannot be by the RadialJets/CutFamily route
* `RadialJets` growth fails for `ψ = V` and `ψ = log(1+V)` (H2), exactly because `L V = -V²+2V+4`, so `Lψ ≤ -(V-5) ~ -e^{ψ}` (`L_psi_le`).
* The stronger by-hand claim of AUDIT_R19_CORE2ELL §6 (no `CutFamily` at all; radialisation + polar-coordinate ODE `|χ̄'(r)| ≤ K/(2 sinh r)`,
  `∫^∞ dr / sinh r` convergent at infinity in the sense `½ log coth(r0/2) → 0`) was NOT formalised (rotation averaging, geodesic polar coordinates and the radial
  reduction of `L`; estimate 800-1200 lines).  I re-derived the computation by hand: `m(r) = sinh r e^{-2cosh r}`, `∫_r^∞ m = e^{-2cosh r}/2`, hence `|χ̄'(r)| ≤ K/(2 sinh r)`; it stands.
* Precise missing estimate for a `Core2` proof for `hypRiem` that avoids `CutFamily`: in `core2_of_ZL_ell` the cut-off error terms `v Lχ_n`, `Lχ_n Lv`, `Γ(χ_n,Lv)`,
  `v LLχ_n`, `Γ(Lχ_n,v)`, `Γ₂(χ_n,v)` for `χ_n = σ(ψ/n)`, `ψ = log(1+V)`, are of size `V^k/n`, `k ≤ 3`, so one needs (heuristic count, not checked) the weighted bounds
  `V^k v, V^k Γ(v)^{1/2}, V^k Γ₂'(v)^{1/2}, V^k Lv ∈ L²(μ)`, `k ≤ 3`, for `v = (1-L)^{-1}a`, `a ∈ C_c^∞`.  The Gibbs-on-`ℝ^d` analogue
  (R19-Rd-3, `memLp_V_mul_of_hardy`, one power of the weight) exists only for Gibbs data; its `EllData`/Riemannian version with such powers is not in the repository, not attempted.
* The converse of Prop. 3.3.17 for `hypRiem` does not need this: it is already proved without `Core2` (`hypRiem_mem_domain_of_Γ₂_direct`, R20).

### (ii) two charts / atlas
Not done.  Assessment: an honest `RiemData`-over-atlas needs (a) manifold structure with transition maps and chartwise `RiemData` compatible on overlaps (co-metric `g' = J g Jᵀ`,
`W` a function, density by `|det J|`), (b) invariance of `L`, `Γ`, `Γ₂` under chart changes (chain rule to order 2 for `L`, 3 for `Γ₂`; each a 200-400 line coordinate computation in this library,
cf. `CurvCov.lean`, `CurvInv.lean`, which already treat covariance of the curvature objects), (c) global `L²(μ)`, `𝒜₀ = C_c^∞(M)` via a partition of unity and chartwise regularity.
Rough estimate 2500-4000 lines; nothing closes cheaply.

### (iii) non-compact finite-`n` CD with `ρ ≤ 0`
Already in the repository (not new): `lebesgueFull : FullTriple ℝ`, `μ` = Lebesgue (infinite), `𝒜₀ = C_c^∞`, `𝒜 = C^∞`, `lebesgue_CD : ρ ≤ 0 → 1 ≤ n → CD ρ n` (all `n ∈ [1,∞]`, including `n = 1`).
This is a genuinely non-compact finite-`n` instance with `𝒜 ≠ 𝒜₀` (so the R16/R17 "no such instance" scope notes are accurate only for `ρ > 0` or `d ≥ 2`).  New here: sharpness
`lebesgue_CD_iff` (`CD ρ n ↔ ρ ≤ 0 ∧ 1 ≤ n`; test function `f(x) = x`, `Γ₂ = 0`, `Γ = 1`), `lebesgueFull_noncompact`, `lebesgueFull_A_ne_A₀` (`1 ∈ 𝒜 \ 𝒜₀`).
NOT done: `(ℝ^d, Lebesgue)`, `d ≥ 2`, or hyperbolic space with `W = 0`, as a `FullTriple`.  Obstruction: `EllData`/`RiemData` require `integrable` (finite `μ`) and the `fullU`
construction (S10, S11, F8, F10) uses the probability measure; the infinite-volume case needs the heat-kernel route of `Lebesgue/{Heat,Identify,ODE,...}.lean` (about 2600 lines in 1-D) redone in `ℝ^d`
(a tensorisation theorem for `FullTriple` is absent), and for hyperbolic space S11 (stochastic completeness) under `Ric ≥ -1` without a heat kernel is a separate theorem.
A pointwise `CD(-1,2)` for `W = 0` is not available from `RiemData` either (`hypRiem` has weight `W = 2cosh d`, `n = ∞`, `Curv 1`, `hypRiem.curv`).

## Proposed ERRATA rows (not added; ERRATA.md untouched)
| R22-E4-1 | INFO (correction) | R16/R17 scope notes say no non-compact finite-`n` `CD` instance with `𝒜 ≠ 𝒜₀` exists. | `lebesgueFull` (`ℝ`, `𝒜₀ = C_c^∞ ≠ 𝒜 = C^∞`, infinite `μ`) satisfies `CD(ρ,n)` iff `ρ ≤ 0 ∧ 1 ≤ n` (`lebesgue_CD_iff`); `ρ > 0` and `d ≥ 2` remain open. |
| R22-E4-2 | INFO | `hypRiem`: `RadialJets` fails for `V` and `log(1+V)` (`hypRiem.hyp_not_radialJets_V/_psi`, `L V = -V²+2V+4`). | `CoreCut` for `hypRiem` stays false by hand (AUDIT_R19 §6, not formalised). |
| R22-E4-3 | LOW (naming) | The new hyperbolic theorems are in namespace `...Riemannian.hypRiem`. | |
Proposed imports in `MarkovTriple.lean`: `...Riemannian.R22.NonCompactCD`, `...R22.HypCutObstruction`, `...R22.AxiomCheckR22E4`.
