# Round 15 self-audit: weighted Euclidean (Gibbs on `ℝ^d`) and weighted Riemannian (global chart) instances

Armstrong step (b): the author attacks his own statements (`Instances/STATEMENTS_R15_Riem.md`) before handing them to an
independent hostile auditor.  Files: `Instances/GibbsRd/*.lean`, `Instances/Riemannian/*.lean`.  Every Lean fact quoted
below is a theorem of the library (standard axioms only, see the two `AxiomCheck.lean`), unless marked "by inspection".

## 0. Mathlib survey (decision for part C)

Read in this Mathlib (`v4.35.0-rc2`): `Geometry/Manifold/Riemannian/{Basic,PathELength}` (Riemannian metric as an inner
product on tangent spaces, the extended distance as an infimum of lengths, `IsRiemannianManifold`),
`Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic,Metric,Torsion,LeviCivita}` (covariant derivatives, the
Levi-Civita connection, Koszul formula, uniqueness), `Geometry/Euclidean/Volume/Measure` (Euclidean Hausdorff measure on
`EuclideanSpace`).  **Absent**: any Riemannian volume (density) measure on a manifold, the Laplace–Beltrami operator,
the Hessian of a function, the Riemann/Ricci tensor, the Bochner–Lichnerowicz formula (grep for `ricci` finds nothing;
`curvature` finds nothing in `Geometry`).  Consequently a *faithful intrinsic* `DiffusionTriple` of a weighted
Riemannian manifold `(M, g, e^{-W}dμ_g)` is not realistic with the current library: one would first have to construct
the measure `μ_g` from charts (partition of unity + change of variables), the Laplacian, the Hessian and Ricci tensors and
prove the Bochner identity.  The tractable faithful route chosen (and used by the book itself, Sect. 1.11.2–1.11.3 and
C.3) is the **coordinate definition**: co-metric `g^{ij}`, `w_g = det(g^{ij})^{-1/2}`,
`Δ_g f = w_g⁻¹ Σ ∂ᵢ(w_g g^{ij} ∂ⱼ f)`, `L = Δ_g − ∇W·∇`, in a single global chart `ℝ^d`.  A torus `ℝ^d/ℤ^d` with
periodic data was not attempted: it needs the quotient measure, the quotient test algebra and the periodic calculus
(only the one-dimensional circle exists in the library).

## 1. What was proved (summary)

* `EllData d` (smooth symmetric positive definite `a = g^{ij}` bounded above, smooth positive integrable `w`) and its
  `DiffusionTriple` `E.diff` with ALL of D1–D8 (including density of `C_c^∞` in every `L^p(μ)`, exhaustion sequence
  `cut (n+1)`, `ibp` by Mathlib's Fréchet integration by parts, `∫ L f = 0`); `ΓA_eq`; change of variables for `Γ` and
  `L` on `C^∞` (BGL (3.1.2), (3.1.8)); `diff_isComplete` (Def. 3.3.9, cut-offs `ζ_k = cut (M(k+1))`); `preFull`
  (F1, F2, F4–F7, F9 on `𝒜 = C^∞`); under named `WeakHypo`: ESA, ergodicity; with `Curv ρ`: Poincaré, spectral gap, `L²`
  decay; with `F8`: the Full triple, `CD(ρ,∞)`, conditional LSI/gradient bound.
* Gibbs on `ℝ^d`: `Lr V = Δ − ∇V·∇`, `gibbsRd_Γ₂_eq` (Bochner (1.16.5), every smooth `f`, every `x`), `gibbsRd_curv`,
  `integrable_of_convex_rd`, `gaussData`, `gaussData_curv`, `gauss_not_curv_two` (sharpness), `Lr_restr1`/`Gr_restr1`
  (`d = 1` agrees with `Gibbs/Calculus`).
* Riemannian chart: `RiemData`, `riem_L_eq` ((1.11.10)), `ell_L_coord` ((1.11.8)), `ofGibbs_toEll_L` (flat consistency),
  `diagRiem` (a genuinely variable co-metric `diag(2 + sin xᵢ)` with `W = |x|²/2`), and the same layers as above.

## 2. Attacks on the statements, and results

### 2.1 Vacuity
* *Is `EllData`/`GibbsRdData`/`RiemData` inhabited?*  Yes: `gaussData d` (any `d`), `GibbsRdData.ofConvex`, `diagRiem d`,
  `RiemData.ofGibbs`.  All fields of each structure are proved, none assumed.
* *Is the hypothesis `Curv ρ` trivially true or false?*  Neither: `gaussData_curv : Curv 1` holds and
  `gauss_not_curv_two : ¬ Curv 2` (witness `f(x) = x₀`, `d ≥ 1`) — the Poincaré constant `1/ρ = 1` of the Gaussian is sharp.
* *Is `Hess V ≥ ρ` satisfiable with `ρ > 0` beyond the Gaussian?*  `integrable_of_convex_rd` shows every such `V` yields
  integrable `e^{-V}`; examples are the usual uniformly convex potentials (by inspection; only `|x|²/2` is built).
* `WeakHypo` and `F8` are *named hypotheses* (as in the 1-D library).  They are (mathematically) true: `WeakHypo` is elliptic
  regularity for a formally self-adjoint elliptic operator with smooth coefficients (weak `L² ` solutions of `L f = λ f` tested
  against `C_c^∞` are smooth), `F8` is smoothing of the Friedrichs semigroup.  They are NOT proved here and have no Lean
  proof in the repository (not for `d = 1` either); every theorem below them says "under `WeakHypo`".  `Curv ρ`,
  `EntropyInterpolation`, `GradientInterpolation` likewise.
* Non-vacuity of the conclusions `PI`, `HasSpectralGap`: they are only asserted under the named hypotheses; the
  combined statement for the Gaussian is therefore a conditional theorem, not an unconditional one.

### 2.2 Junk values, partial functions
* `pderiv f i x = fderiv f x eᵢ` is `0` where `f` is not differentiable.  Every statement about `L`, `Γ₂`, `ΓA` that depends
  on derivatives of order ≥ 2 assumes `Sm f` (smooth) explicitly: `toEll_L`, `riem_L_eq`, `ell_L_coord`, `gibbsRd_Γ₂_eq`,
  `ΓA_eq`, `Curv` (quantifies over `Sm f`).  `toEll_Γ` holds for *all* `f, g` (both sides are the same junk-free sum).
* The `DiffusionTriple` constrains `L`, `Γ` only on `𝒜₀ = C_c^∞` (smooth), so the junk of `E.L` off `C²` is invisible.
* `Z = ∫ w` is the Bochner integral of an integrable positive function: `Z > 0` is proved (`Z_pos`, using that `volume ≠ 0`
  on `Fin d → ℝ`, also for `d = 0` where `Rd 0` is a point and `volume univ = 1`).
* `w_g = det(g^{ij})^{-1/2}` is `Real.rpow` with base `det > 0` (proved from `Matrix.PosDef.det_pos`), so no junk.
* `d = 0` is allowed and harmless (all sums empty; `a_pos` vacuous; `Curv` vacuous: Γ = 0).  The probe `gauss_not_curv_two`
  needs `[NeZero d]`.

### 2.3 a.e. versus everywhere
All identities (`ΓA_eq`, `L_comp`, `Γ_comp`, `gibbsRd_Γ₂_eq`, `riem_L_eq`, `ell_L_coord`, `Curv`) are pointwise-everywhere
for smooth functions, which is stronger than the a.e. readings of the frozen structures (`μ` has a positive density, so for
continuous functions a.e. equality is equivalent to everywhere equality anyway).  `IsComplete` and the D-fields are
a.e. statements in the frozen definitions and are proved via everywhere statements.

### 2.4 Fidelity to the book (conventions)
* Co-metric convention: BGL p. 46–47 write `g = (g^{ij})` for the *co-metric* and `w_g = det(g)^{-1/2}`; Appendix C.4: "the
  Riemannian measure has density `det(g)^{-1/2}` with `det(g)` the determinant of the matrix `(g^{ij})`".  `RiemData.g`
  is the co-metric, `wg = det(g^{ij})^{-1/2}`, so `μ_g` is `√det(g_{ij}) dx` as it must be.
* `Γ(f,g) = Σ g^{ij} ∂ᵢf ∂ⱼg` is (1.11.2); the divergence-form `L` is (1.11.8)/(1.11.10); `∫ g L f dμ = −∫ Γ(f,g) dμ`
  is `EllData.ibp_sm` (1.11.9).
* `Γ₂` is the library's formula-defined `½(LΓ(f) − 2Γ(f,Lf))` (Def. 3.3.12, `DiffusionTriple.Γ₂`), not a re-definition.
* Bochner `Γ₂ = Σ(∂ⱼ∂ᵢ f)² + Σ ∂ⱼ∂ᵢV ∂ᵢf ∂ⱼf` is (1.16.5) with the Euclidean Hilbert–Schmidt norm.
* Dimension `n < ∞` of `CD(ρ,n)` is NOT claimed (false for non-constant `V`, `V` const is not integrable).

### 2.5 Deliberate scope limits (candid)
1. **Bochner–Lichnerowicz for variable `g` (BGL (1.16.4), Thm C.3.3) is not proved.**  `Curv ρ` for Riemannian data is a
   pointwise hypothesis on the formula-defined `Γ₂`; its identification with `Ric_g + ∇∇W ≥ ρ g` is open.  For `g = δ` it is
   proved (part B).  `diagRiem` is only an inhabitant of `RiemData`; no curvature statement is claimed for it.
2. Global chart only (`ℝ^d`); no atlas, no non-trivial topology; `μ` must be finite (no Lebesgue / hyperbolic space).
3. `a_bdd` (upper bound of the co-metric) is used only for completeness; it is not needed for D1–D8.  A non-complete chart
   (e.g. `a` unbounded) is excluded by hypothesis, not by a theorem; completeness of a *general* complete Riemannian chart
   with unbounded co-metric is not proved (cut-offs by the Riemannian distance are not available).
4. Not done: unconditional `WeakHypo`, `F8`, LSI, gradient bound for any of these triples (same status as the 1-D Gibbs case).

### 2.6 Hidden dependencies
`GibbsRd/EllPI.lean` imports `Instances/Gibbs/FunctESA` and `FunctPreFull` only for the generic `PreFull`,
`DiffusionTriple.WeakHypoElliptic`, `ESAProp_of_weakHypo`, `ergodic_of_weakHypo`, which live in files named `Gibbs/Funct*` but
are stated for an arbitrary `DiffusionTriple`.  `GibbsRd/Convex.lean` imports the 1-D `Gibbs.quad_lower`.  No existing file
was edited (only `MarkovTriple.lean` got imports, `ERRATA.md` rows R15-1..5, `frozen-manifest.json` one new `proposed`
entry; old hashes unchanged, `scripts/check_frozen.py` prints `OK`).

## 3. Attack surface for the independent auditor

1. Definition of `EllData.L` (divergence form with `w⁻¹`): is it the book's operator?  (`ell_L_coord`, `riem_L_eq`,
   `toEll_L` say yes for smooth `f`; check against (1.11.8) and (1.11.10) by reading.)
2. `ibp_master` / `ibp_sm` (every `DiffusionTriple` field `ibp`, `integral_L`): verify the compact-support hypotheses
   (`hcs_*`) and that `integral_pderiv_eq_zero` really uses Lebesgue (not `μ`) measure, with `μ = Z⁻¹ w dx` and `integral_dens_mul`.
3. `EllData.diff` field `dense`: density in `L^p(μ)` for `1 ≤ p < ∞` of `C_c^∞` through `Lp.dense_hasCompactSupport_contDiff`.
4. `diff_isComplete`: cut-off constants (`M = 1 + 8|Λ|C²`, `sT_deriv_bound`, `sum_sq_pderiv_cut_le`); `Γ(ζ_k) ≤ 1/(k+1)²`
   must hold everywhere, as stated by `IsComplete`.
5. `preFull.connected`: `Γ f f = 0 a.e. ⇒ f const` uses `a_pos` (strict positivity) and continuity (`Continuous.ae_eq_iff_eq`
   needs `μ` open-positive: `instIsOpenPosMeasure`).
6. `Curv` (A6/R15-2) is quantified over `Sm f` only; `full_CD` transfers it to `FullTriple.CD` on `Afull`; confirm the
   frozen `CD` really is `ρΓ + (∞⁻¹).toReal (Lf)² ≤ Γ₂` (yes: `simp` with `ENNReal.inv_top`).
7. `gibbsRd_Γ₂_eq` against the formula in (1.16.5); `third_symm`/`pderiv_symm` (symmetric Hessian from
   `ContDiffAt.isSymmSndFDerivAt`); `alg_bochner` (finite-sum bookkeeping).
8. `integrable_of_convex_rd`: via the ray `t ↦ t x` and the 1-D `Gibbs.quad_lower`; `deriv_deriv_ray`.
9. `RiemData`: `g_posDef` (Mathlib `Matrix.PosDef`), `g_symm` redundancy with Hermitian-ness (harmless), `integrable`
   (statement uses `det^(-1/2)` literally).  `diagRiem.integrable` (bounded by the Gaussian since `det ≥ 1`).
10. Statement files: `STATEMENTS_R15_Riem.md` (registered `proposed`), errata `R15-1..5`; the Lean names in the statement
    file differ from the final ones only as logged.
11. Named hypotheses `WeakHypo`, `F8`, `Curv`, `EntropyInterpolation`, `GradientInterpolation`: confirm each theorem lists
    exactly the hypotheses it uses (`ell_poincare`: `Curv ρ`, `WeakHypo`, `ρ > 0` only).
12. `ofGibbs_toEll_L`: the flat Riemannian operator equals the Gibbs operator for ALL `f` (equal `a`, `w` ⇒ equal `L`).
