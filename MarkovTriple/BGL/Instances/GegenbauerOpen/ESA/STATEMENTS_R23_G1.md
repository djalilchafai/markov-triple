# STATEMENTS R23-G1 -- F10 (essential self-adjointness) for the zonal Gegenbauer triple `goDiff` (lambda = 3/2) on (-1,1)

Method "Armstrong": statements written before any proof.  Namespace `MarkovTriple.BGL.Instances.GegenbauerOpen` (helper lemmas in
`...GegenbauerOpen.ESA`), directory `MarkovTriple/BGL/Instances/GegenbauerOpen/ESA/`.

## Route chosen: (B), a direct Weyl limit-point argument in 1-D, with the abstract part already in the library

* Route (A) (transfer from `Instances/Sphere`) is NOT used: it needs a zonal reduction `S^4 -> (-1,1)` of the generator and
  Gegenbauer eigenfunction machinery not present in the library; Route (C) (cut-off + Hardy) needs log-scale cut-offs with explicit
  `L^2(mu)` bounds on `L(theta_n)` (the linear-scale cut-off gives `||L theta||_{L^2(mu)} = O(1)`, not `o(1)`).
* Route (B) is elementary.  Reduction (abstract, = the second half of `DiffusionTriple.core_of_invariant` in `Semigroup/ESA.lean`):
  `(1 - L) C_c^inf` dense in `L^2(mu)` implies `ESAProp`.  Density means: `w in L^2(mu)`, `<(1-L)a, w> = 0` for all `a in C_c^inf((-1,1))`
  forces `w = 0`.  With `p = (1-x^2)^2`, `W = 1 - x^2`, `W L f = (p f')'`, `u = w` a representative: `int_{(-1,1)} u W (f - L f) dx = 0`.
  (i) Regularity (du Bois-Reymond, via Fubini/a.c. integration by parts): such `u` equals a.e. a function `v` with
      `v' = F/p`, `F' = W v` on `(-1,1)` (classical derivatives).
  (ii) Weyl: `v, F` as in (i) with `int W v^2 < infinity` satisfy `v = 0`.  Proof: `Y = F v` has `Y' = W v^2 + F^2/p >= 0`; if `Y(t0) > 0` for
      some `t0 > 0` then `F` has constant sign, `|F| >= f0 > 0` on `[t0,1)`, `v' >= f0/p >= f0/(4(1-x)^2)`, `v >= c/(1-x)` near 1,
      `W v^2 >= c'/(1-x)` not integrable: contradiction.  Hence `Y <= 0` on `(0,1)`; by monotonicity of `Y`, `Y <= 0` on `(-1,1)`.
      By the reflection `x -> -x` (`v~(x) = v(-x)`, `F~(x) = -F(-x)`), `Y >= 0`.  So `Y = 0`, `Y' = 0`, `v = 0`.
      (This is the limit-point property at both endpoints: the singular solution `~ (1-x)^{-1}` is not in `L^2(W dx)`.)

## Statements

```lean
namespace MarkovTriple.BGL.Instances.GegenbauerOpen.ESA

/-- (ii) one endpoint -/
theorem weyl_end (v F : ℝ → ℝ)
    (hv : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt v (F x / (1 - x ^ 2) ^ 2) x)
    (hF : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt F ((1 - x ^ 2) * v x) x)
    (hint : IntegrableOn (fun x => (1 - x ^ 2) * v x ^ 2) (Ioo (0:ℝ) 1)) :
    ∀ t ∈ Ioo (0:ℝ) 1, F t * v t ≤ 0

/-- (ii) both endpoints -/
theorem weyl (v F : ℝ → ℝ)
    (hv : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt v (F x / (1 - x ^ 2) ^ 2) x)
    (hF : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt F ((1 - x ^ 2) * v x) x)
    (hint : IntegrableOn (fun x => (1 - x ^ 2) * v x ^ 2) (Ioo (-1:ℝ) 1)) :
    ∀ x ∈ Ioo (-1:ℝ) 1, v x = 0

/-- (i) regularity of weak solutions of `(L - 1) u = 0` -/
theorem weak_regular (u : ℝ → ℝ)
    (hint : IntegrableOn (fun x => (1 - x ^ 2) * u x ^ 2) (Ioo (-1:ℝ) 1))
    (hmeas : AEStronglyMeasurable u (volume.restrict (Ioo (-1:ℝ) 1)))
    (hweak : ∀ f ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, u x * ((1 - x ^ 2) * (f x - goL f x)) = 0) :
    ∃ v F : ℝ → ℝ, (∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt v (F x / (1 - x ^ 2) ^ 2) x) ∧
      (∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt F ((1 - x ^ 2) * v x) x) ∧
      ∀ᵐ x ∂(volume.restrict (Ioo (-1:ℝ) 1)), u x = v x

/-- (iii) deficiency vectors vanish -/
theorem go_orth_zero (w : Lp ℝ 2 goμ) (h : ∀ a : goDiff.A₀, inner ℝ (goDiff.cls a - goDiff.Lcls a) w = 0) : w = 0

/-- (iv) abstract reduction -/
theorem esaProp_of_orth (T : DiffusionTriple E) (h : ∀ w : Lp ℝ 2 T.μ,
    (∀ a : T.A₀, inner ℝ (T.cls a - T.Lcls a) w = 0) → w = 0) : T.ESAProp

/-- **F10 for `goDiff`** -/
theorem go_esaProp : goDiff.ESAProp
```

## DIFFERENCE FROM BGL

BGL (Ch. 3, Prop. 3.3.11 and the discussion of Gegenbauer / Jacobi operators) gives ESA of `L` on polynomials; here the core is
`C_c^inf((-1,1))`, a deliberately different algebra (R22-E2).  Both are for `lambda = 3/2` only (`n = 4`).  Nothing else deviates:
`ESAProp` is the library's F10 (`Theory/ESAOne.lean`) verbatim.

## Status

**`go_esaProp : goDiff.ESAProp` is PROVED** (F10 for the zonal Gegenbauer `lambda = 3/2` triple on `(-1,1)` with `C_c^inf((-1,1))`).
Build of `ESA.{Weyl,Prim,Regularity,Main,AxiomCheckR23G1}`: 0 errors, 0 warnings, no `sorry`, no `set_option`; axioms of every
theorem below are only `propext`, `Classical.choice`, `Quot.sound` (`AxiomCheckR23G1.lean`).  No frozen file, `lakefile.toml`,
`lake-manifest.json`, toolchain, `ERRATA.md`, `GAPS.md`, `MarkovTriple.lean` touched.

Theorems (statements as in the block above; nothing weakened):
* `Weyl.lean`: `weyl_end`, `weyl` (limit-point at both endpoints; the key non-integrability is `weyl_core` + `not_integrableOn_div_one_sub`).
* `Prim.lean`: `LocInt` and calculus on it; `ibp_primitive` (integration by parts against an absolutely continuous primitive, via Mathlib's
  `AbsolutelyContinuousOnInterval`), `primitive_mem`, `kernel_trick`, `dbr1` (du Bois-Reymond; uses Mathlib's
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
* `Regularity.lean`: `ibp_I`, `locInt_of_L2`, `weak_step1`, **`weak_regular`**.
* `Main.lean`: **`DiffusionTriple.esaProp_of_orth`** (abstract: `(1-L)A0` dense in `L^2` implies `ESAProp`; the second half of
  `core_of_invariant`, restated without the semigroup hypothesis), **`go_orth_zero`** (stated for `w : Lp ℝ 2 goμ`, which is
  `Lp ℝ 2 goDiff.μ` by `rfl`), **`go_esaProp`**.

Deviations: none from the statements as first written.  (Notes: `go_orth_zero` uses `goμ` in place of `goDiff.μ`, definitional.
`weak_regular` is stated with `∫ x in Ioo (-1) 1, u x * ((1 - x^2) * (f x - goL f x)) = 0`; the transfer from the `L^2(goμ)` inner
product is inside `go_orth_zero`, constant `3/4` removed.)  Mathematical remark: the proof uses only `W = 1-x^2` and `p = W^2`
(`∫ dx/(1-x)` diverges and `p ≤ 4(1-x)^2`), i.e. the `lambda = 3/2` limit-point computation; for `lambda < 3/2` the singular solution is
square-integrable and ESA fails (ERRATA R21-4).

What remains for a `FullTriple` on `goDiff` (R22-E2 S3): F10 is now closed; still open: F8 (interior smoothness of `P_t f`), F1-F7, F9, F2
(elementary, est. 400-600 lines as in R22-E2), S10 (ergodicity).  S11 now follows from `DiffusionTriple.conservative_of_esa` (finite
measure) applied to `go_esaProp`.  With `go_not_complete` and `goDiff_CD`, a `FullTriple` on `goDiff` would be a non-complete CD(3,4) one.

### Proposed ERRATA / GAPS rows (ERRATA.md/GAPS.md NOT edited)
| id | severity | finding | resolution |
|---|---|---|---|
| R23-G1-1 | INFO | `go_esaProp : goDiff.ESAProp`: F10 holds for the zonal Gegenbauer triple `lambda = 3/2` on `(-1,1)` with `C_c^inf((-1,1))` (limit-point at both endpoints; Weyl argument + regularity of weak solutions, in Lean). | `Instances/GegenbauerOpen/ESA/*` |
| R23-G1-2 | INFO (GAPS) | GAPS R21-4 / R22-E2-3: the F10 part is closed for `lambda = 3/2`; a `FullTriple` on `goDiff` still needs F8, F1-F7, F9, S10 (S11 follows from `conservative_of_esa`). | this Status |
| R23-G1-3 | INFO | `DiffusionTriple.esaProp_of_orth`: `ESAProp` follows from density of `(1-L)𝒜₀` alone (no semigroup invariance). | `ESA/Main.lean` |

### Import lines for `MarkovTriple.lean` (not edited by me)
```
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.Weyl
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.Prim
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.Regularity
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.Main
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.AxiomCheckR23G1
```
and `frozen-manifest.json` has one `proposed` entry for this file.
