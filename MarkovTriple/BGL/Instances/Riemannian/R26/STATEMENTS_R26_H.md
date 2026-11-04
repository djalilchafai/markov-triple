# Round 26, Stream H (atlas gluing): frozen target statements

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.Instances.Riemannian.R26`; files `Instances/Riemannian/R26/*`.
No existing file is edited (except `MarkovTriple.lean` imports, `GAPS.md`, `ERRATA.md`).  `𝕋 = AddCircle 1` (the library circle,
`Sanity.Circle`), `A₀ = Sanity.Circle.A₀`, `Gc f h = D f * D h`, `Lc f = D (D f)`, `μ₀ = haarAddCircle`; `circleCompact`, `circle_CD` (Circle/Triple).

## SCOPE (honest)
Full multi-chart gluing for general `d` (Piola identity for `L`, partitions of unity on abstract manifolds, `C^∞(M)` as `𝒜₀`) is NOT attempted.
Delivered target, following BGL Appendix C.3 / Sect. 1.11.3 (coordinate co-metric `g`, `w_g = det(g)^{-1/2}`, `L = (1/w)∂(w g ∂)`):
* H1: coordinate invariance of the carré du champ under a change of chart, any dimension `d` (chain rule + pushforward of the co-metric);
* H2: dimension `d = 1`: a chart datum, chartwise `Γ`, `L` computed from `(g, w)`, proved equal to the intrinsic `Gc`, `Lc` on `𝒜₀` (coordinate invariance of
  `Γ` and `L`), concrete stereographic charts of `𝕋` (north/south), the transition-map formulas (`g_b∘τ = τ'² g_a`, `w_a = (w_b∘τ)|τ'|`);
* H3: an atlas (cover by charts), glued `Γ`, `L` (value computed in any chart containing the point), independent of the chart chosen;
* H4: the Riemannian measure glued by a partition of unity `ρ_N = cos²(πx)`, `ρ_S = sin²(πx)` from the chartwise volume `w dt`, equal to `μ₀`;
* H5: the `DiffusionTriple 𝕋` built from the atlas data coincides (fields `μ, Γ, L`) with `circleDiffusion`; `Γ₂` and `CD(ρ,n)` computed from the glued data.
The sphere `S²` is not covered (the library "sphere" is the zonal `S³`, a one-dimensional reduction; no genuine multi-chart `S^d`, `d ≥ 2`).

## H1: `R26/ChartChange.lean`
```
theorem gamma_chart_change {d : ℕ} (ga gb : Fin d → Fin d → (Fin d → ℝ) → ℝ) (τ : (Fin d → ℝ) → (Fin d → ℝ))
    (F H : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (hτ : DifferentiableAt ℝ τ x)
    (hF : DifferentiableAt ℝ F (τ x)) (hH : DifferentiableAt ℝ H (τ x))
    (hg : ∀ i j, gb i j (τ x) = ∑ k, ∑ l, pderiv (fun y => τ y i) k x * ga k l x * pderiv (fun y => τ y j) l x) :
    ∑ i, ∑ j, gb i j (τ x) * pderiv F i (τ x) * pderiv H j (τ x) =
      ∑ k, ∑ l, ga k l x * pderiv (F ∘ τ) k x * pderiv (H ∘ τ) l x
```

## H2: `R26/Chart1.lean` (d = 1)
```
structure Chart1 where  (x : ℝ → ℝ) (smooth : ContDiff ℝ ⊤ x) (dpos : ∀ t, 0 < deriv x t)
noncomputable def Chart1.pt (c) (t : ℝ) : 𝕋 := (c.x t : 𝕋)
noncomputable def Chart1.g (c) (t) : ℝ := (deriv c.x t)⁻¹ ^ 2          -- co-metric
noncomputable def Chart1.w (c) (t) : ℝ := deriv c.x t                    -- w_g = g^{-1/2}
noncomputable def Chart1.Γ (c) (f h : 𝕋 → ℝ) (t : ℝ) : ℝ := c.g t * deriv (fun u => f (c.pt u)) t * deriv (fun u => h (c.pt u)) t
noncomputable def Chart1.L (c) (f : 𝕋 → ℝ) (t : ℝ) : ℝ :=
    (c.w t)⁻¹ * deriv (fun u => c.w u * c.g u * deriv (fun v => f (c.pt v)) u) t        -- (1/w) (w g F')'
theorem Chart1.Γ_eq (c) {f h} (hf : f ∈ A₀) (hh : h ∈ A₀) (t) : c.Γ f h t = Gc f h (c.pt t)
theorem Chart1.L_eq (c) {f} (hf : f ∈ A₀) (t) : c.L f t = Lc f (c.pt t)
def northChart, southChart : Chart1        -- x t = arctan t / π ,  arctan t / π + 1/2   (stereographic charts)
theorem north_g (t) : northChart.g t = π^2 * (1+t^2)^2 ;  theorem north_w (t) : northChart.w t = 1/(π*(1+t^2))
theorem north_south_pt {t} (ht : t ≠ 0) : northChart.pt t = southChart.pt (-1/t)           -- transition τ(t) = -1/t
theorem transition_g {t} (ht : t ≠ 0) : southChart.g (-1/t) = (1/t^2)^2 * northChart.g t
theorem transition_w {t} (ht : t ≠ 0) : northChart.w t = southChart.w (-1/t) * |1/t^2|
theorem chart_transition (a b : Chart1) {t s} (h : a.pt t = b.pt s) {f h'} (hf) (hh) : a.Γ f h' t = b.Γ f h' s ∧ a.L f t = b.L f s
```

## H3: `R26/Atlas1.lean`
```
structure Atlas1 where (ι : Type) (chart : ι → Chart1) (cover : ∀ p : 𝕋, ∃ i t, (chart i).pt t = p)
noncomputable def Atlas1.glueΓ (A) (f h) (p : 𝕋) : ℝ     -- (chart i).Γ f h t for (i,t) := choose (cover p)
noncomputable def Atlas1.glueL (A) (f) (p : 𝕋) : ℝ
def stereoAtlas : Atlas1                                  -- ι = Bool, charts north/south
theorem Atlas1.glueΓ_eq (A) (hf) (hh) : A.glueΓ f h = Gc f h ;  theorem Atlas1.glueL_eq (A) (hf) : A.glueL f = Lc f
theorem Atlas1.glueΓ_indep (A) (i t) (hp : (A.chart i).pt t = p) : A.glueΓ f h p = (A.chart i).Γ f h t        -- any chart containing p
```

## H4: `R26/Measure.lean`
```
theorem integral_north (F : 𝕋 → ℝ) (hF : Continuous F) : ∫ t, F (northChart.pt t) * northChart.w t = ∫ p, F p ∂μ₀
theorem integral_south (same, southChart)
noncomputable def atlasIntegral (F : 𝕋 → ℝ) : ℝ :=        -- partition of unity ρ_N = cos²(π x), ρ_S = sin²(π x)
    ∫ t, ρN (northChart.pt t) * F (northChart.pt t) * northChart.w t + ∫ t, ρS (southChart.pt t) * F (southChart.pt t) * southChart.w t
theorem atlasIntegral_eq (F) (hF : Continuous F) : atlasIntegral F = ∫ p, F p ∂μ₀
```

## H5: `R26/AtlasTriple.lean`
```
noncomputable def atlasDiff : DiffusionTriple 𝕋     -- μ := μ₀ (= glued Riemannian volume, `atlasIntegral_eq`), A₀ := A₀, Γ := stereoAtlas.glueΓ, L := stereoAtlas.glueL
theorem atlasDiff_Γ : atlasDiff.Γ = circleDiffusion.Γ ;  theorem atlasDiff_L : atlasDiff.L = circleDiffusion.L
theorem atlasDiff_Γ₂ {f} (hf : f ∈ A₀) (x) : atlasDiff.Γ₂ f f x = (stereoAtlas.glueL f x)^2
theorem atlas_CD {ρ} (hρ : ρ ≤ 0) {n} (hn : 1 ≤ n) {f} (hf : f ∈ A₀) (x) :
    ρ * stereoAtlas.glueΓ f f x + (n⁻¹).toReal * (stereoAtlas.glueL f x)^2 ≤ atlasDiff.Γ₂ f f x
```
Pre-announced fallback: if `H4` (change of variables) does not close, `atlasDiff` takes `μ := μ₀` directly and H4 is reported as not proved.
(The measure of `atlasDiff` is `μ₀` in all cases; `atlasIntegral_eq` is the statement that this is the atlas-glued Riemannian volume.)
