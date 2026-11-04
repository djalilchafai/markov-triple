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
(filled at the end)
