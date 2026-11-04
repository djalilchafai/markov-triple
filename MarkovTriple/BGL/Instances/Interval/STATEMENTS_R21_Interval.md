# STATEMENTS R21 -- the interval triple (0,1): a concrete NON-COMPLETE Markov triple

Method "Armstrong": statements first (this section was written before any proof; deviations are logged
in `## Status`).  Namespace `MarkovTriple.BGL.Instances.Interval`, files
`MarkovTriple/BGL/Instances/Interval/{Basic,Diffusion,NotComplete,NotESA}.lean`, `AxiomCheckR21.lean`.

Purpose: show that `DiffusionTriple.IsComplete` (Def. 3.3.9, `Frozen/Complete.lean`) is a genuine
hypothesis of the Round 20 direct converse (`FullTriple.mem_domain_of_Γ₂_direct`, ERRATA R20-M1): a
diffusion triple with `Γ₂ ≥ 0`-type curvature but NOT complete, and (consistently) not a `FullTriple`.

CORRECTION to the informal brief: the interval triple is NOT a `FullTriple` (F10, ESA, fails for
`(0,1)`), and BGL completeness is a `Γ`-cut-off condition, not geodesic completeness.  So CD on a
`FullTriple` cannot even be stated for it; the honest statements are below.

## Data

State space `E = ℝ` with `μ = volume.restrict (Ioo 0 1)` (reason: the whole real-variable calculus of
`Instances/Lebesgue` is reused verbatim; with the subtype `↥(Ioo 0 1)` one would re-do derivatives on a
subtype for nothing; functions of `𝒜₀` are defined on all of `ℝ` but vanish outside `(0,1)`, and only their
restriction to `(0,1)` is seen by `μ`).

```lean
noncomputable abbrev ivμ : Measure ℝ := volume.restrict (Set.Ioo (0:ℝ) 1)
/-- C_c^∞((0,1)): smooth f : ℝ → ℝ with tsupport f ⊆ Ioo 0 1 (hence compact support). -/
def ivA₀ : NonUnitalSubalgebra ℝ (ℝ → ℝ)   -- carrier {f | Sm f ∧ tsupport f ⊆ Set.Ioo 0 1}
/-- L f = f'', Γ(f,g) = f' g' (as in the ℝ case: `Lebesgue.Lf`, `Lebesgue.Gf`). -/
noncomputable def ivDiff : DiffusionTriple ℝ   -- μ := ivμ, A₀ := ivA₀, Γ := Lebesgue.Gf, L := Lebesgue.Lf
```

## Statements

* **I1** `ivDiff : DiffusionTriple ℝ`, all fields proved (D1 finite_prob: `μ = Lebesgue` on `(0,1)` is a
  probability measure -- note total mass is 1 so `finite_prob` needs no sorry; D2 density of `ivA₀` in every
  `Lᵖ((0,1))`, `1 ≤ p < ∞`; exhaustion `u_n = ST((n+1)x-1)·ST((n+1)(1-x)-1)`; IBP and chain rule from the ℝ case).
* **I2** (pointwise Γ₂ and curvature).
  `theorem iv_Γ₂_eq {f} (hf : Lebesgue.Sm f) (x : ℝ) : ivDiff.Γ₂ f f x = (deriv (deriv f) x)^2`,
  i.e. `ivDiff.Γ₂ f f x = (f'' x)^2` for every smooth `f` (the candidate extended algebra `𝒜 = C^∞`),
  and `ivDiff.ΓA f g x = f' x * g' x` for smooth `f, g`.  CD form (the body of `FullTriple.CD`, which needs a
  `FullTriple` and so is unavailable here):
  `def IvCD (ρ : ℝ) (n : ℝ≥0∞) : Prop := 1 ≤ n ∧ ∀ f, Sm f → ∀ x, ρ * ivDiff.ΓA f f x + (n⁻¹).toReal * (Lf f x)^2 ≤ ivDiff.Γ₂ f f x`
  `theorem ivDiff_CD {ρ : ℝ} {n : ℝ≥0∞} (hρ : ρ ≤ 0) (hn : 1 ≤ n) : IvCD ρ n`
  (in particular CD(0,n) for every `n ≥ 1`, and CD(0,∞)).
* **I3** `theorem iv_not_complete : ¬ ivDiff.IsComplete`.
* **I4** (ESA fails, in the library's own formulation `DiffusionTriple.ESAProp`, which is F10 verbatim):
  `theorem iv_not_esaProp : ¬ ivDiff.ESAProp`, and
  `theorem iv_no_fullTriple (T : FullTriple ℝ) : T.toDiffusionTriple ≠ ivDiff`
  ("no `FullTriple` structure has `ivDiff` as its underlying diffusion triple").  Auxiliary:
  `theorem iv_exp_orth` : `u = exp|_(0,1)` is `L²(μ)`, nonzero and `∫ u (f'' - f) dμ = 0` for all `f ∈ ivA₀`
  (so `(L - 1)𝒜₀` is not dense in `L²`; the deficiency subspace of `L|𝒜₀` is nonzero).
* **I5** (stretch) bounded open interval `(a,b)` / bounded open `Ω ⊂ ℝ`: see Status.
* **I6** research note (no Lean): see Status.

## DIFFERENCE FROM BGL

1. BGL's `𝒜₀` for a domain `Ω` is `C_c^∞(Ω)`; same here.  Elements are functions `ℝ → ℝ` (extension by `0`);
   `μ` is the restricted Lebesgue measure, so `μ`-a.e. statements only see `(0,1)`.  Equivalent to the book's
   `E = (0,1)`.
2. `CD` is stated as `IvCD` (the body of `FullTriple.CD` with `T.A` replaced by `C^∞` and the a.e. statement
   made pointwise), NOT as `FullTriple.CD`, because by I4 no `FullTriple` over `ivDiff` exists.  BGL itself
   treats CD for `Γ₂` on the extended algebra `𝒜 = C^∞(Ω)`, which is exactly what `IvCD` does.
3. No deviation in `IsComplete` or `ESAProp` (used verbatim).

## Status

I1-I4 are PROVED, with statements exactly as written above (nothing weakened; the only edits to this file after
the proofs: the typo `toΓ₂`, the `Lebesgue.Sm` qualifier, the file location, and this Status).  `lake build` of
the modules below: 0 errors, 0 warnings, no `sorry`, no `set_option`; axioms: only `propext`, `Classical.choice`,
`Quot.sound` (`AxiomCheckR21.lean`).  No frozen file, `lakefile.toml`, `lake-manifest.json`, toolchain touched.

Files (all under `MarkovTriple/BGL/Instances/Interval/`; this statements file lives there too, repo convention):
`Basic.lean` (`ivμ`, `ivA₀`, cut-offs `ivcut`, density `ivA₀_dense`), `Diffusion.lean` (`ivDiff`, `iv_ΓA`,
`iv_Γ₂_eq`, `IvCD`, `ivDiff_CD`), `NotComplete.lean` (`abs_le_of_Γ`, `iv_not_complete`), `NotESA.lean`
(`iv_exp_ibp`, `memLp_exp_iv`, `iv_exp_orth`, `iv_not_esaProp`, `iv_no_fullTriple`), `AxiomCheckR21.lean`.

* I1 `ivDiff : DiffusionTriple ℝ`: every field proved (reusing the `Lebesgue.*` calculus).  The only real work is
  `ivA₀_dense`, density of `C_c^∞((0,1))` in `Lᵖ((0,1))`, `1 ≤ p < ∞`: Mathlib's `MemLp.exist_eLpNorm_sub_le`
  for `μ = ivμ` gives `g ∈ C_c^∞(ℝ)`; multiply by the cut-off `ivcut n` (supported in `[1/(n+1), 1-1/(n+1)]`) and
  the error is `‖(1-ivcut n) g‖_p ≤ ‖g‖_∞ (4/(n+1))^{1/p} → 0`.
* I2 `iv_Γ₂_eq`: `Γ₂ f f x = (f'' x)²` for ALL smooth `f` (library `Γ₂`, built from the formula `ΓA`);
  `ivDiff_CD`: `IvCD ρ n` for every `ρ ≤ 0`, `n ∈ [1,∞]`.
* I3 `iv_not_complete : ¬ ivDiff.IsComplete`, proof as suggested (uses only `ζ_k ∈ 𝒜₀`, `ζ_k → 1` a.e., and
  `Γ ζ_k ≤ 1/(k+1)²`; monotonicity/positivity of `ζ_k` are not needed).
* I4 `iv_not_esaProp : ¬ ivDiff.ESAProp` (`ESAProp` = F10 verbatim, `Theory/ESAOne.lean`), `iv_no_fullTriple`.
  Proof: `u = exp|_(0,1)` is orthogonal to `(L-1)𝒜₀` (`iv_exp_orth`); the resolvent `R u` lies in the Friedrichs domain
  and `(G-1) R u = -u` (library `FormData.generator_R`); ESA would give `a_n ∈ 𝒜₀` with `a_n → R u`, `L a_n → G R u`
  in `L²`, so `0 = ⟨u,(L-1)a_n⟩ → ⟨u,-u⟩ = -‖u‖²`.

### Consistency with BGL (Dirichlet vs Neumann)
`L = d²/dx²` on `C_c^∞(0,1)` has deficiency indices `(2,2)`: its closure has domain `H²_0`, the Friedrichs extension (the
library's `generator`) is the Dirichlet Laplacian (`H² ∩ H¹_0`), the Neumann Laplacian is another self-adjoint
extension, so `L|𝒜₀` is not essentially self-adjoint.  BGL's F10 (Def. 3.1.10) excludes this case; nothing contradicts
the book (the book states the interval as the typical non-ESA example).  `exp ∈ ker(L*-1)` is the elementary witness.

### What this shows for the Round 20 direct converse (ERRATA R20-M1) -- honest scope
`FullTriple.mem_domain_of_Γ₂_direct` needs a `FullTriple` that is complete.  The interval triple is a genuine
`DiffusionTriple` with `Γ₂ = (f'')² ≥ (Lf)²/n` (CD(0,n) in the shape `IvCD`) but is NOT complete (I3), and,
independently, is NOT a `FullTriple` (I4).  Consequences: (a) completeness is not implied by CD(0,n) plus the
diffusion-triple axioms; (b) the interval triple is NOT a counterexample to the converse inside its hypotheses:
being outside `FullTriple` it is excluded regardless of completeness.  Hence it does NOT prove that completeness is
needed within `FullTriple` + `CD`.  A non-complete `FullTriple` is the content of I6 and is NOT established here.

### I5 (bounded open interval `(a,b)` / bounded open `Ω ⊂ ℝ`): OPEN, not done
For `(a,b)` it is an affine transport (`x ↦ (x-a)/(b-a)`) of every proof (cut-off rescaled, `Γ` scales by
`(b-a)^{-2}`), est. 150-300 lines.  For general bounded open `Ω ⊂ ℝ` one needs cut-offs on countably many
components and `|ζ(x)| ≤ dist(x,∂Ω) sup|ζ'|`, est. 400+ lines.  Not attempted.

### I6 research note: does a non-complete `FullTriple` exist?  (nothing in this section is proved in Lean)
Candidate: zonal Gegenbauer on `(-1,1)`, `L = (1-x²) f'' - (2λ+1) x f'`, `Γ(f,g) = (1-x²) f' g'`, weight
`(1-x²)^{λ-1/2}`, `𝒜₀ = C_c^∞(-1,1)`, i.e. `S^n` (`n = 2λ+1`) with the poles removed, zonal part.
 * CORRECTION to the brief's range `λ ≥ 1/2`.  Hand computation (Weyl alternative): `Lf = 0` has solutions `1` and
   `f ~ (1-x)^{1/2-λ}` (`log` if `λ = 1/2`) near `1`; `|f|²·weight ~ (1-x)^{1/2-λ}` is integrable iff `λ < 3/2`.  So
   the endpoints are limit-circle for `λ < 3/2` (`n = 2,3`: then `L|𝒜₀` is NOT ESA, as for the interval) and
   limit-point iff `λ ≥ 3/2`, i.e. `n ≥ 4` (this matches my recollection that `Δ` on `S^n` minus two points is ESA iff `n ≥ 4`).  So the range for which F10 can hold
   is `λ ≥ 3/2`, not `λ ≥ 1/2`.  This was derived by hand and has not been cross-checked against a reference.
 * Non-completeness for every `λ > 0`: `∫_{-1}^{1} dx/√(1-x²) = π < ∞`, i.e. the `Γ`-distance between the endpoints
   is finite (`π`), so `ζ_k ∈ C_c^∞(-1,1)`, `ζ_k → 1`, `|ζ_k'| √(1-x²) ≤ 1/(k+1)` is impossible: `ζ_k(x) ≤ (arcsin x + π/2)/(k+1) ≤ π/(k+1) → 0`.
   This is the formalizable unconditional part (the analogue of I3, ~60 lines) but it needs the `DiffusionTriple` for the
   weighted operator on `(-1,1)` (weighted IBP, chain rule, density of `C_c^∞(-1,1)` in `Lᵖ(μ)`, exhaustion):
   est. 600-900 lines; the library's Gibbs files assume `V` smooth on all of `ℝ` and cannot be reused directly.
 * ESA of `L` on `C_c^∞(-1,1)` (F10) for `λ ≥ 3/2`: needs the limit-point criterion (Weyl) or capacity cut-offs
   (log-cut-offs at `±1`, `‖ζ_k'‖_{L²(w(1-x²))} → 0`, ~300 lines) plus graph-norm density from the polynomial core
   (compact-triple route) (~500 lines), plus the extended algebra `C^∞(-1,1)` and F1-F9 (~800 lines, F8/F9 risky).
   Several weeks of work, high risk.  I make NO claim that a non-complete `FullTriple` exists.
 * Remark (research suggestion, not a result): for `n ≥ 4` the same generator would be presented by the complete
   triple `𝒜₀ = C^∞(S^n)` (`CompactTriple.isComplete`) and by the non-complete `𝒜₀ = C_c^∞(S^n ∖ poles)`, so completeness
   would be a property of the test algebra `𝒜₀`, not of the generator.

### Proposed ERRATA rows (for the maintainer; ERRATA.md/GAPS.md NOT edited)
| id | severity | finding | resolution |
|---|---|---|---|
| R21-1 | INFO (scope) | Completeness (Def. 3.3.9) is a genuine hypothesis at the `DiffusionTriple` level: `((0,1), Lebesgue, C_c^∞((0,1)))` is a `DiffusionTriple` with `Γ₂ f = (f'')² = (Lf)²` (EQUALITY, so `Γ₂ ≥ (Lf)²/n` for every `n ≥ 1`; `ivDiff_CD` is therefore cheap and is not CD in the sense of the book's Def. 3.3.x, audit L3/L5) but `¬ IsComplete` (`iv_not_complete`). | `Instances/Interval/*` |
| R21-2 | INFO (correction) | The interval triple is NOT a `FullTriple`: F10 fails (`iv_not_esaProp`, `iv_no_fullTriple`; deficiency vector `exp`). So it does not show that completeness is needed inside the hypotheses of `FullTriple.mem_domain_of_Γ₂_direct` (R20-M1); whether a non-complete `FullTriple` with CD exists is OPEN (I6). | `NotESA.lean`; GAPS: non-complete `FullTriple` open |
| R21-3 | LOW (doc) | `FullTriple.CD` exists only for `FullTriple`s, so CD cannot be stated for the interval triple; `IvCD` (same body, pointwise, all smooth `f`) is used. | `Diffusion.lean` |
| R21-4 | INFO (correction) | Gegenbauer without poles: F10 can hold only for `λ ≥ 3/2` (`n ≥ 4`), by hand computation, not `λ ≥ 1/2`. | I6 above; verified independently by the hostile audit (L1): endpoints limit-circle for `λ < 3/2`, limit-point iff `λ ≥ 3/2`; the earlier `λ ≥ 1/2` conjecture was wrong |

### Import lines for `MarkovTriple.lean` (not edited by me)
```
import MarkovTriple.BGL.Instances.Interval.Basic
import MarkovTriple.BGL.Instances.Interval.Diffusion
import MarkovTriple.BGL.Instances.Interval.NotComplete
import MarkovTriple.BGL.Instances.Interval.NotESA
import MarkovTriple.BGL.Instances.Interval.AxiomCheckR21
```
and `frozen-manifest.json` gets one `proposed` entry for this file (added with `scripts/check_frozen.py --update`).
