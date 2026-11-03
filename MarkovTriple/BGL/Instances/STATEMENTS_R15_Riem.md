# Round 15: target statements, weighted Euclidean (Gibbs on `ℝ^d`) and weighted Riemannian (coordinate) instances

Armstrong method: this file is written BEFORE any proof.  Later changes only through a logged erratum in `ERRATA.md`
(prefix `R15-`).  Book = Bakry–Gentil–Ledoux (BGL), *Analysis and Geometry of Markov Diffusion Operators*.
Namespace of all Lean names: `MarkovTriple.BGL.Instances.GibbsRd` (Euclidean/generic) and
`MarkovTriple.BGL.Instances.Riemannian` (coordinate Riemannian).  Space: `Rd d := Fin d → ℝ` with Lebesgue = product
measure, `d : ℕ` arbitrary (the case `d = 0` is the one-point space and is allowed, harmless).
`∂ᵢ f := BGL.pderiv f i` (`= Df(·)(eᵢ)`), `∂ⱼ∂ᵢ f := pderiv (pderiv f i) j`.  `Sm f := ContDiff ℝ ⊤ f`.
`A₀ d := C_c^∞(ℝ^d)` (non-unital algebra), `Afull d := C^∞(ℝ^d)`.

## What the book gives (the definitions are BGL's own coordinate formulas)

* Sect. 1.11.2 (1.11.1)–(1.11.9): operator `L f = Σ g^{ij}∂²ᵢⱼ f + Σⱼ (Σᵢ ∂ᵢ g^{ij} + g^{ij} ∂ᵢ log w) ∂ⱼ f` has
  `Γ(f,g) = Σ g^{ij} ∂ᵢf ∂ⱼg` and is symmetric w.r.t. `dμ = w dx`; `∫ f Lg dμ = −∫ Γ(f,g) dμ`.
* Sect. 1.11.3 (p. 46–47, (1.11.10)): co-metric `g = (g^{ij})`, Riemannian measure density `w_g = det(g)^{-1/2}`,
  `Δ_g f = (1/w_g) Σ ∂ᵢ(w_g g^{ij} ∂ⱼ f)`, weighted `L = Δ_g − ∇W·∇`, `dμ = e^{-W} dμ_g`.
* (1.16.4)–(1.16.5), Def 1.16.1, (1.16.8): `Γ₂(f) = |∇∇f|² + Ric(L)(∇f,∇f)`; on `ℝ^n` with flat metric
  `Γ₂(f) = |∇∇f|² + ∇∇W(∇f,∇f)`; `CD(ρ,∞)` iff `Ric + ∇∇W ≥ ρ g`.
* Defs 3.1.1, 3.1.3, 3.1.8, hypotheses D1–D8; Def 3.3.1, 3.3.7–3.3.9, Props 3.3.10–3.3.11 (completeness, weak
  hypo-ellipticity, ESA, ergodicity); Def 3.3.14 (`CD(ρ,n)`); Cor 4.8.2/Prop 4.8.3 (Poincaré from `CD(ρ,∞)`).

## Part A: generic weighted elliptic operator on `ℝ^d` (`GibbsRd/Ell*.lean`)

```
structure EllData (d : ℕ) where
  a : Fin d → Fin d → Rd d → ℝ          -- (g^{ij}) : co-metric / diffusion matrix
  w : Rd d → ℝ                           -- reversible density of L w.r.t. dx (unnormalised)
  a_smooth : ∀ i j, Sm (a i j)
  a_symm   : ∀ i j x, a i j x = a j i x
  a_pos    : ∀ x (v : Rd d), v ≠ 0 → 0 < ∑ i, ∑ j, a i j x * v i * v j      -- elliptic
  a_bdd    : ∃ Λ : ℝ, ∀ x (v : Rd d), ∑ i, ∑ j, a i j x * v i * v j ≤ Λ * ∑ i, v i ^ 2   -- complete
  w_smooth : Sm w
  w_pos    : ∀ x, 0 < w x
  integrable : Integrable w volume
-- normalising constant Z := ∫ w ; μ := Z⁻¹ w dx  (probability measure)
def Γ  f g x := ∑ i, ∑ j, a i j x * ∂ᵢf x * ∂ⱼg x
def L  f x   := (w x)⁻¹ * ∑ i, ∂ᵢ (fun y => w y * ∑ j, a i j y * ∂ⱼ f y) x     -- = (1/w) div(w a ∇f)
```

* **A1** `EllData.diff : DiffusionTriple (Rd d)` with `μ = ell.μ`, `A₀ = A₀ d`, `Γ`, `L` as above: all of D1–D8
  (every field proved, none assumed).  `IsProbabilityMeasure ell.μ`.
* **A2** `EllData.ΓA_eq : f g smooth → diff.ΓA f g = Γ f g` (everywhere): the formula-defined `Γ` of Def 3.3.1 (iv)
  equals the coordinate carré du champ.
* **A3** `EllData.diff_isComplete : diff.IsComplete` (Def 3.3.9) — proved from `a_bdd` with explicit cut-offs.
* **A4** `EllData.preFull : PreFull diff (Afull d)` (F1, F2, F4–F7, F9 of Def 3.3.1/3.3.7 on `𝒜 = C^∞`).
* **A5** (Props 3.3.10–3.3.11, conditional on `EllData.WeakHypo := diff.WeakHypoElliptic (Afull d)`, Def 3.3.8)
  `diff_esaProp : WeakHypo → diff.ESAProp` (F10) and `diff_ergodic : WeakHypo → …` (S10).
* **A6** (integrated curvature) `integral_Γ₂ : f ∈ A₀ d → ∫ Γ₂ f f dμ = ∫ (L f)² dμ` (BGL (3.3.8)),
  for `Γ₂ = diff.Γ₂` (Def 3.3.12); `integrated_CD`: if `∀ f ∈ Afull, ∀ x, ρ Γ f f x ≤ diff.Γ₂ f f x` (the pointwise
  `CD(ρ,∞)` of Def 3.3.14, a named hypothesis `Curv ρ`) then `ρ ∫Γ(f) ≤ ∫(Lf)²` on `A₀ d`.
* **A7** `ell_poincare : 0<ρ → Curv ρ → WeakHypo → diff.PI (1/ρ)` and `ell_spectralGap`, `ell_expDecay`
  (Cor 4.8.2/Prop 4.8.3).  Hypotheses are exactly: `Curv ρ` (Def 3.3.14 with `n = ∞` on smooth functions) and
  `WeakHypo` (Def 3.3.8).
* **A8** `EllData.standard (hH)`, `EllData.full (hH) (h8) : FullTriple (Rd d)` with `F8 := ∀ t f, ∃ g ∈ Afull, P_t f =ᵐ g`
  (Def 3.3.1 (viii)); `full_CD : Curv ρ → (full hH h8).CD ρ ∞`; `full_logSobolev`, `full_gradient_bound` conditional on
  the repository's named structures `EntropyInterpolation`, `GradientInterpolation` exactly as in the 1-D Gibbs case.

## Part B: Gibbs measure `e^{-V}dx` on `ℝ^d`, trivial metric (`GibbsRd/Gibbs*.lean`)

```
structure GibbsRdData (d : ℕ) where
  V : Rd d → ℝ ; smooth : Sm V ; integrable : Integrable (fun x => exp (-V x))
def GibbsRdData.toEll : EllData d   -- a i j x = if i = j then 1 else 0 ; w = exp (-V)
def Lr V f x := ∑ i, (∂ᵢ∂ᵢ f x − ∂ᵢ V x * ∂ᵢ f x)        -- Δ f − ∇V·∇f ,  Γ f g x = ∑ ∂ᵢf ∂ᵢg
```

* **B1** `gibbsRdDiff : DiffusionTriple (Rd d)` (:= `toEll.diff`), `μ = Z⁻¹ e^{-V}dx`, `A₀ = C_c^∞`,
  `L = Lr V`, `Γ = Σ ∂ᵢf∂ᵢg` (the equalities `toEll`-`L` = `Lr`, `toEll`-`Γ` = trivial one are PROVED lemmas
  `toEll_L`, `toEll_Γ`, so the instance has the book's `L = Δ − ∇V·∇`).  `gibbsRdDiff_isComplete`.
* **B2 (Bochner, BGL (1.16.5))** for `f` smooth and every `x`:
  `gibbsRdDiff.Γ₂ f f x = Σᵢⱼ (∂ⱼ∂ᵢ f x)² + Σᵢⱼ ∂ⱼ∂ᵢV x · ∂ᵢf x · ∂ⱼf x`.
* **B3** if `Hess V ≥ ρ`, i.e. `∀ x v, ρ Σ vᵢ² ≤ Σᵢⱼ ∂ⱼ∂ᵢV x vᵢ vⱼ`, then `ρ Γ f f x ≤ Γ₂ f f x` for every smooth `f`,
  every `x` (`Curv ρ`).
* **B4 (non-vacuity)** a uniformly convex `V` (`Hess V ≥ ρ > 0`) has integrable `e^{-V}`
  (`GibbsRdData.ofConvex`), and `V = |x|²/2` is the standard Gaussian on `ℝ^d` (`Hess V = 1`).
* **B5** `gibbsRd_poincare : 0<ρ → HessV ≥ ρ → WeakHypo → gibbsRdDiff.PI (1/ρ)`; spectral gap `ρ`; `L²` decay;
  `gibbsRdFull hH h8 : FullTriple (Rd d)` and `gibbsRdFull_CD : (…).CD ρ ∞` for `Hess V ≥ ρ`;
  `gibbsRdFull_logSobolev`, `gibbsRdFull_gradient_bound` conditional on `EntropyInterpolation`,
  `GradientInterpolation`.
* NOT claimed: finite `n` in `CD(ρ,n)` (false for non-constant `V`; `V` const is not integrable), unconditional
  F8/WeakHypo (open in the 1-D library too), LSI/gradient bound unconditionally.

## Part C: weighted Riemannian metric in global coordinates on `ℝ^d` (`Riemannian/*.lean`)

```
structure RiemData (d : ℕ) where
  g : Fin d → Fin d → Rd d → ℝ               -- co-metric (g^{ij}) of BGL Sect. 1.11.3
  W : Rd d → ℝ
  g_smooth : ∀ i j, Sm (g i j) ; g_symm : ∀ i j x, g i j x = g j i x
  g_posDef : ∀ x, (Matrix.of fun i j => g i j x).PosDef
  g_bdd    : ∃ Λ, ∀ x v, Σᵢⱼ g i j x vᵢ vⱼ ≤ Λ Σ vᵢ²           -- metric ≥ Λ⁻¹ Euclid: complete
  W_smooth : Sm W
  integrable : Integrable (fun x => exp (-W x) * (det (g x))^(-1/2))
def wg x := (Matrix.det (Matrix.of fun i j => g i j x)) ^ (-1/2 : ℝ)       -- Riemannian density w_g
def Δg f x := (wg x)⁻¹ * ∑ i, ∂ᵢ (fun y => wg y * ∑ j, g i j y * ∂ⱼ f y) x   -- Laplace–Beltrami
def toEll : EllData d    -- a = g, w = exp(-W) * wg
```

* **C1** `riemDiff : DiffusionTriple (Rd d)` (:= `toEll.diff`), with `Γ(f,g) = Σ g^{ij} ∂ᵢf ∂ⱼg` and
  `L f = Δg f − Σᵢⱼ g^{ij} ∂ᵢW ∂ⱼ f` (**(1.11.10)**, lemma `riem_L_eq`); `L f x = Σ g^{ij}∂ⱼ∂ᵢ f + Σⱼ (Σᵢ ∂ᵢ g^{ij} +
  g^{ij} ∂ᵢ log w) ∂ⱼ f` with `w = e^{-W} wg` (**(1.11.8)**, lemma `riem_L_coord`).
* **C2** `riemDiff_isComplete` (Def 3.3.9; the co-metric bound `g_bdd` makes the Euclidean cut-offs `ζ_k` satisfy
  `Γ(ζ_k) ≤ Λ/(k+1)²`, which is the usual "Euclidean complete + metric ≥ c·Euclid ⇒ complete").
* **C3** flat consistency: for `g = δ`, `toEll`-`L` is `Lr W` (so Part B is the case `g = δ` of Part C).
* **C4** `riemPreFull`, ESA/ergodicity (conditional on `WeakHypo`), `riem_poincare`, `riemFull`, `riemFull_CD`
  exactly as A4–A8, with the curvature hypothesis `Curv ρ` stated as the pointwise
  `ρ Γ(f) ≤ Γ₂(f)` (Def 3.3.14) for the formula-defined `Γ₂ = ½(LΓ(f)−2Γ(f,Lf))`.
* NOT claimed (and why, to be documented): the identification `Γ₂ = |∇∇f|² + (Ric_g + ∇∇W)(∇f,∇f)` for variable `g`
  (BGL (1.16.4), Thm C.3.3).  It is the Bochner–Lichnerowicz identity in coordinates: it needs Christoffel symbols,
  the Riemann/Ricci tensor and a long tensor computation that Mathlib does not provide; the library therefore
  states `CD` for Riemannian data only through the book's *definition* (pointwise `Γ₂ ≥ ρ Γ`), not through
  `Ric + Hess W ≥ ρ g`.  Also not covered: manifolds that are not global charts (no atlas calculus / Hausdorff
  Riemannian volume in Mathlib), periodic metrics on the torus (needs the quotient measure and
  periodic-function calculus; only the 1-circle exists in the library), infinite `μ` (Lebesgue/hyperbolic) for
  Part C (here `integrable` is required, as for the 1-D `GibbsData`).
