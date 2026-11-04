# Round 27, Stream J (atlas gluing beyond d = 1): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.Instances.Riemannian.R27`; files `Instances/Riemannian/R27/*`.  Only `MarkovTriple.lean`, `GAPS.md`,
`ERRATA.md`, `frozen-manifest.json` are edited outside this directory.  Follows the four-step plan of GAPS "Round 26, Stream H" and BGL Appendix C.3
(co-metric `g = (g^{ij})`, Riemannian density `w = det(g)^{-1/2}`, `L F = (1/w) Σ_i ∂_i (w Σ_j g^{ij} ∂_j F)`).
NOTE on conventions: `g` is the CO-metric (inverse of the round metric), so on `S²` in a stereographic chart `g^{ij} = ((1+|y|²)/2)² δ_{ij}` and
`w = 4/(1+|y|²)²` (the metric itself is `4/(1+|y|²)² δ`).

## SCOPE (honest)
Algebraic/analytic atlas gluing of the operators `Γ`, `L`, `Γ₂` (pointwise, with explicit `C²` hypotheses).  No topology/smooth-manifold structure on `M` is
used or constructed (the atlas is a family of parametrisations with transition maps and laws); no `DiffusionTriple`, `FullTriple`, semigroup, `C^∞(M)`-density or
partition-of-unity measure for `S²` is attempted.  `CD(1,2)` for `S²` is NOT proved as an inequality for all functions; only the coordinate functions are
checked chartwise (equality case).

## J0: common definitions (`R27/Basic.lean`)
```
abbrev Ev (d : ℕ) := Fin d → ℝ
noncomputable def jac {d} (τ : Ev d → Ev d) (x : Ev d) : Matrix (Fin d) (Fin d) ℝ := fun a b => pderiv (fun y => τ y a) b x
noncomputable def Gch {d} (g : Fin d → Fin d → Ev d → ℝ) (F H : Ev d → ℝ) (x : Ev d) : ℝ :=
    ∑ i, ∑ j, g i j x * pderiv F i x * pderiv H j x
noncomputable def Lch {d} (g : Fin d → Fin d → Ev d → ℝ) (w : Ev d → ℝ) (F : Ev d → ℝ) (x : Ev d) : ℝ :=
    (w x)⁻¹ * ∑ i, pderiv (fun y => w y * ∑ j, g i j y * pderiv F j y) i x
```

## J1: Piola identity and `L` under change of chart, any `d` (`R27/Piola.lean`, `R27/LChange.lean`)
```
theorem piola_identity {d} (τ : Ev d → Ev d) (x : Ev d) (hτ : ContDiffAt ℝ 2 τ x) (i : Fin d) :
    ∑ k, pderiv (fun y => (jac τ y).adjugate k i) k x = 0

theorem Lch_chart_change {d} (ga gb : Fin d → Fin d → Ev d → ℝ) (wa wb : Ev d → ℝ) (τ : Ev d → Ev d) (F : Ev d → ℝ) (x : Ev d)
    (hτ : ContDiffAt ℝ 2 τ x) (hF : ContDiffAt ℝ 2 F (τ x))
    (hga : ∀ i j, ContDiffAt ℝ 1 (ga i j) x) (hwa : ContDiffAt ℝ 1 wa x)
    (hgb : ∀ i j, ContDiffAt ℝ 1 (gb i j) (τ x)) (hwb : ContDiffAt ℝ 1 wb (τ x))
    (hwa0 : wa x ≠ 0)
    (hg : ∀ᶠ z in 𝓝 x, ∀ i j, gb i j (τ z) = ∑ k, ∑ l, jac τ z i k * ga k l z * jac τ z j l)
    (hw : ∀ᶠ z in 𝓝 x, wa z = wb (τ z) * |(jac τ z).det|) :
    Lch gb wb F (τ x) = Lch ga wa (F ∘ τ) x
```
(`Gch gb F H (τ x) = Gch ga (F∘τ) (H∘τ) x` is the existing `R26.gamma_chart_change`; restated as `Gch_chart_change` under pointwise hypotheses.)

## J2: general atlas, independence from the transition laws (`R27/Atlas.lean`)
```
structure Chart (M : Type) (d : ℕ) where
  U : Set (Ev d) ; isOpen : IsOpen U ; pt : Ev d → M ; injOn : Set.InjOn pt U
  g : Fin d → Fin d → Ev d → ℝ ; w : Ev d → ℝ
  g_smooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (g i j) U ; w_smooth : ContDiffOn ℝ (⊤ : ℕ∞) w U ; w_pos : ∀ x ∈ U, 0 < w x
def Chart.overlap (a b : Chart M d) : Set (Ev d) := {x | x ∈ a.U ∧ ∃ y ∈ b.U, b.pt y = a.pt x}
structure Atlas (M : Type) (d : ℕ) where
  ι : Type ; chart : ι → Chart M d ; cover : ∀ p : M, ∃ i, ∃ x ∈ (chart i).U, (chart i).pt x = p
  τ : ι → ι → Ev d → Ev d
  overlap_open : ∀ a b, IsOpen ((chart a).overlap (chart b))
  τ_mem : ∀ a b, ∀ x ∈ (chart a).overlap (chart b), τ a b x ∈ (chart b).U ∧ (chart b).pt (τ a b x) = (chart a).pt x
  τ_smooth : ∀ a b, ContDiffOn ℝ 2 (τ a b) ((chart a).overlap (chart b))
  τ_g : ∀ a b, ∀ x ∈ (chart a).overlap (chart b), ∀ i j,
    (chart b).g i j (τ a b x) = ∑ k, ∑ l, jac (τ a b) x i k * (chart a).g k l x * jac (τ a b) x j l
  τ_w : ∀ a b, ∀ x ∈ (chart a).overlap (chart b), (chart a).w x = (chart b).w (τ a b x) * |(jac (τ a b) x).det|
def Atlas.Smooth (A : Atlas M d) (k : ℕ) (f : M → ℝ) : Prop := ∀ i, ContDiffOn ℝ k (f ∘ (A.chart i).pt) (A.chart i).U
noncomputable def Atlas.glueΓ (A) (f h : M → ℝ) (p : M) : ℝ      -- Gch in the chart chosen by `cover p`
noncomputable def Atlas.glueL (A) (f : M → ℝ) (p : M) : ℝ         -- Lch in the chart chosen by `cover p`
theorem Atlas.glueΓ_indep (A) {f h} (hf : A.Smooth 2 f) (hh : A.Smooth 2 h) (i) {x} (hx : x ∈ (A.chart i).U) :
    A.glueΓ f h ((A.chart i).pt x) = Gch (A.chart i).g (f ∘ (A.chart i).pt) (h ∘ (A.chart i).pt) x
theorem Atlas.glueL_indep (A) {f} (hf : A.Smooth 2 f) (i) {x} (hx : x ∈ (A.chart i).U) :
    A.glueL f ((A.chart i).pt x) = Lch (A.chart i).g (A.chart i).w (f ∘ (A.chart i).pt) x
def Atlas.glueΓ₂ (A) (f : M → ℝ) (p : M) : ℝ := (1/2) * A.glueL (A.glueΓ f f) p - A.glueΓ f (A.glueL f) p
theorem Atlas.glueΓ₂_indep (A) {f} (hf : A.Smooth 4 f) (i) {x} (hx : x ∈ (A.chart i).U) :
    A.glueΓ₂ f ((A.chart i).pt x) =
      (1/2) * Lch (A.chart i).g (A.chart i).w (fun y => Gch (A.chart i).g (f ∘ (A.chart i).pt) (f ∘ (A.chart i).pt) y) x
        - Gch (A.chart i).g (f ∘ (A.chart i).pt) (fun y => Lch (A.chart i).g (A.chart i).w (f ∘ (A.chart i).pt) y) x
```
(Independence is derived from `τ_*` and `Lch_chart_change`/`Gch_chart_change` only; no global operator.)

## J3: the sphere `S²` with two stereographic charts (`R27/Sphere2.lean`)
```
def S2 : Type := {p : Fin 3 → ℝ // p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1}
noncomputable def sphereAtlas : Atlas S2 2           -- ι = Bool; both charts U = univ; pt σ y = (2y₀, 2y₁, σ(|y|²-1))/(1+|y|²), σ = ±1;
                                                     -- g^{ij} = ((1+|y|²)/2)² δ_ij, w = 4/(1+|y|²)²; τ a b = id if a = b, y ↦ y/|y|² otherwise
theorem sphereAtlas_overlap_ne : (sphereAtlas.chart true).overlap (sphereAtlas.chart false) = {x | x ≠ 0}
theorem sphereAtlas_τ {x} (hx : x ≠ 0) : sphereAtlas.τ true false x = fun i => x i / (x 0 ^ 2 + x 1 ^ 2)
```
(All laws `τ_g`, `τ_w`, smoothness, overlap openness are fields of `sphereAtlas`, hence verified by its construction.)
Chartwise computations on the coordinate functions `coordFn a p = p.1 a`:
```
theorem coordFn_smooth (a) (k) : sphereAtlas.Smooth k (coordFn a)
theorem sphere_glueL_coord (a) : sphereAtlas.glueL (coordFn a) = fun p => -2 * coordFn a p
theorem sphere_glueΓ_coord (a b) : sphereAtlas.glueΓ (coordFn a) (coordFn b) = fun p => (if a = b then 1 else 0) - coordFn a p * coordFn b p
theorem sphere_glueΓ₂_coord (a) : sphereAtlas.glueΓ₂ (coordFn a) = fun p => 1 + coordFn a p ^ 2
theorem sphere_CD12_coord_eq (a) (p) :
    sphereAtlas.glueΓ (coordFn a) (coordFn a) p + (1/2) * sphereAtlas.glueL (coordFn a) p ^ 2 = sphereAtlas.glueΓ₂ (coordFn a) p
```
(The last is `CD(1,2)` at equality: `Γ₂(f) = ρ Γ(f) + (1/n)(Lf)²` with `ρ = 1`, `n = 2`.)

## FALLBACKS (pre-announced)
If the general-`d` Piola identity does not close, `piola_identity`/`Lch_chart_change` are delivered for `d = 2` only (explicit 2×2 adjugate), with the general case reported as not proved.
If `sphere_glueΓ₂_coord` does not close, only `sphere_glueL_coord`/`sphere_glueΓ_coord` are delivered.
