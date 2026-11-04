# STATEMENTS R23-G2 -- the FullTriple over `goDiff` (zonal Gegenbauer lambda=3/2 on (-1,1), A0 = C_c^infty((-1,1))), F10 as hypothesis

Method "Armstrong": statements written before proofs.  Namespace `MarkovTriple.BGL.Instances.GegenbauerOpen`,
directory `MarkovTriple/BGL/Instances/GegenbauerOpen/Full/`.  Parallel stream G1 proves `go_esaProp : goDiff.ESAProp`;
here it is the hypothesis `hF10`.

## Data

```lean
/-- extended algebra -/
def goA : Subalgebra ℝ (ℝ → ℝ) :=  {f | Measurable f ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1) 1)}
```

## Target

```lean
noncomputable def goStandard (hF10 : goDiff.ESAProp) : StandardTriple ℝ      -- toDiffusionTriple = goDiff
noncomputable def goFull (hF10 : goDiff.ESAProp) : FullTriple ℝ              -- A = goA, toDiffusionTriple = goDiff
theorem goFull_toDiffusionTriple (hF10) : (goFull hF10).toDiffusionTriple = goDiff     -- rfl
theorem goFull_CD (hF10) : (goFull hF10).CD 3 4                                          -- and CD ρ n, ρ ≤ 3, 4 ≤ n
theorem goFull_not_complete (hF10) : ¬ (goFull hF10).toDiffusionTriple.IsComplete
```

Field plan (everything except F10 proved):
* F1 ideal, F2 pos_detect, F3 A_comp, F4 L_mem_A, F5, F6 (Γ and L), F7, F9: elementary calculus (local smooth
  modification `exists_smooth_agree` to reduce to globally smooth functions).
* F8 `semigroup_A`: interior elliptic regularity (1-D, local version of `Gibbs/RegCore`) for the resolvent weak equation
  `∫ u L a dμ = ∫ h a dμ`, `a ∈ C_c^∞((-1,1))`, then `P_t = R^{n+1} ψ(R)` as in `Gibbs/RegSemigroup`.
* S10 ergodic: from the same regularity (`h = 0`: `u` smooth, `(1-x²)² u' = c`) and `c ≠ 0 ⇒ u ∉ L²(μ)`.
  (No F10 needed.)
* S11 conservative and F10 `esa`: from `hF10` (S11 via `DiffusionTriple.conservative_of_esa`; F10 is the field `esa`).
* CD: `Γ₂` is local, so for `f ∈ goA` it equals `Γ₂` of a smooth modification; then `goDiff_CD`.

## DIFFERENCE FROM BGL

1. `λ = 3/2` only; test algebra `C_c^∞((-1,1))` and extended algebra `{measurable, C^∞ on (-1,1)}` (BGL's Gegenbauer has polynomials).
2. `goFull` depends on the HYPOTHESIS `hF10 : goDiff.ESAProp` (F10), supplied by the parallel stream G1.
3. Functions are `ℝ → ℝ`, `μ` lives on `ℝ` supported in `[-1,1]`.

## Status

**Everything except F10 is PROVED**: `goFull hF10 : FullTriple ℝ` is built, with `(goFull hF10).toDiffusionTriple = goDiff` (`rfl`,
`goFull_toDiffusionTriple`), `goFull_CD hF10 : (goFull hF10).CD 3 4`, `goFull_CD' : CD ρ n` for `ρ ≤ 3`, `4 ≤ n`, and
`goFull_not_complete hF10`.  Build of `MarkovTriple.BGL.Instances.GegenbauerOpen.Full.{Defs,PreFull,RegLocal,Sem,NotL2,Ergodic,Curv,Main,AxiomCheckR23G2}`:
0 errors, 0 warnings, no `sorry`, no `set_option`, axioms only `propext`, `Classical.choice`, `Quot.sound`
(`AxiomCheckR23G2.lean`, which also covers `goFull`, whose `hF10` is a bound variable, not an axiom).
No frozen file, `lakefile.toml`, `lake-manifest.json`, toolchain, `ERRATA.md`, `GAPS.md`, `MarkovTriple.lean` touched.

Statements are exactly as written above (nothing weakened); the statement of `goFull_CD` is the library's `FullTriple.CD`.

### Where `hF10 : goDiff.ESAProp` is used (exactly two places)
1. the field `esa` of `FullTriple` (it IS F10: `esa := hF10`);
2. S11 `conservative` in `goStandard` (via `DiffusionTriple.conservative_of_esa`, finite measure).

NOT used: S10 (ergodicity, `go_ergodic`: interior regularity + limit-point endpoint, no F10), F8, F1-F7, F9, CD, non-completeness.

### Theorems (namespace `MarkovTriple.BGL.Instances.GegenbauerOpen`)
* `Full/Defs.lean`: `goA`, `goA₀_le_goA`, `exists_smooth_agree(_at)` (globally smooth modification near a compact subset of `(-1,1)`).
* `Full/PreFull.lean`: `goPreFull : PreFull goDiff goA` (F1 `go_ideal`, F2 `go_pos_detect`, F4 `go_L_mem_A`, F5 `go_ΓA_nonneg`, F6-Γ
  `go_diffusion_Γ_A`, F7 `go_ibp_A`, F9 `go_connected`), `go_A_comp` (F3), `go_diffusion_L_A` (F6-L), `go_ΓA_local`.
* `Full/RegLocal.lean`: **`go_reg_C1`, `go_reg_gain`**: local 1-D elliptic regularity for `goL` with test functions in `C_c^∞((-1,1))`
  (du Bois-Reymond, weight `(1-x²)²`), local version of `Gibbs/RegCore`+`RegBridge`.
* `Full/Sem.lean`: `go_resolvent_gain`, `go_resolvent_pow_reg`, **`go_F8`** (`P_t f ∈ 𝒜` for `f ∈ 𝒜₀`, as in `Gibbs/RegSemigroup`:
  `P_t = R^{n+1}ψ(R)` + resolvent weak identity + `go_reg_*`; representatives in `𝒜` are glued with `Measure.eqOn_open_of_ae_eq`).
* `Full/NotL2.lean`: `go_not_integrable_sq` (`(1-x²)²U' = c ≠ 0` ⇒ `U² ∉ L¹(μ)`, the Weyl limit-point mechanism at `x = 1`).
* `Full/Ergodic.lean`: `go_weak_of_generator_zero`, **`go_ergodic`** (S10).
* `Full/Curv.lean`: `goL_ev`, `goΓA_ev`, `goΓ₂_local`, `goA_CD` (locality of `L`, `ΓA`, `Γ₂`; reduction to the smooth case `goDiff_CD`).
* `Full/Main.lean`: `goStandard`, **`goFull`**, `goFull_toDiffusionTriple`, **`goFull_CD`**, `goFull_CD'`, **`goFull_not_complete`**.

### Deviations (nothing weakened)
1. `𝒜 = {Measurable ∧ ContDiffOn ⊤ (Ioo (-1) 1)}` (smooth in the open interval, no condition at endpoints), as planned in STATEMENTS_R22_E2.
2. `CD` holds for every `f ∈ 𝒜`, not only for smooth `f` (locality of `Γ₂`); the a.e. quantifier is over `goμ`, supported on `(-1,1)`.
3. Interior regularity is proved for `u, h ∈ L¹(goμ)` with the explicit formula `(1-x²)² U' = c + ∫₀ˣ (1-y²) h` (used for S10).

### Consequence (once G1 supplies `go_esaProp`)
`goFull go_esaProp` is a non-complete `FullTriple` satisfying `CD(3,4)`.  Against `FullTriple.mem_domain_of_Γ₂_direct` (which needs
completeness) this would show completeness is a genuine hypothesis of that converse; that check against its conclusion is not done here.

### Proposed ERRATA rows (ERRATA.md/GAPS.md NOT edited)
| id | severity | finding | resolution |
|---|---|---|---|
| R23-G2-1 | INFO | `goFull (hF10 : goDiff.ESAProp) : FullTriple ℝ` (zonal Gegenbauer λ=3/2, `𝒜₀ = C_c^∞((-1,1))`, `𝒜 = C^∞((-1,1))`): F1-F9, S10, S11 proved; only F10 is a hypothesis (S11 and `esa` use it). | `Instances/GegenbauerOpen/Full/*.lean` |
| R23-G2-2 | INFO | `goFull_CD : (goFull hF10).CD 3 4` (and `ρ ≤ 3`, `n ≥ 4`) and `goFull_not_complete`: a non-complete Full Markov Triple with `CD(n-1,n)`, `n = 4`, conditional on F10 (stream G1). | `Full/Main.lean` |
| R23-G2-3 | INFO | F8 for an open (non-compact test algebra) space: interior regularity proved locally (`go_reg_C1`, `go_reg_gain`); S10 derived from it plus a limit-point computation (`go_not_integrable_sq`), without F10. | `Full/RegLocal.lean`, `Sem.lean`, `NotL2.lean`, `Ergodic.lean` |

GAPS row R21-4: reduces to the single hypothesis F10 (`go_esaProp`).

### Import lines for `MarkovTriple.lean` (not edited by me)
```
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Defs
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.PreFull
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.RegLocal
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Sem
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.NotL2
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Ergodic
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Curv
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Main
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.AxiomCheckR23G2
```
`frozen-manifest.json` has one `proposed` entry for this file.
