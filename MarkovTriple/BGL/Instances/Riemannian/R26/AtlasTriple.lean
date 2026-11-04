import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R26.Measure
import MarkovTriple.BGL.Instances.Circle.Triple

/-!
# The Diffusion Markov Triple on the circle built from the stereographic atlas

`atlasDiff` has `Γ := stereoAtlas.glueΓ`, `L := stereoAtlas.glueL` (chartwise formulas from `(g, w)`, glued over the cover),
`𝒜₀ = C^∞(𝕋)` and `μ = μ₀`, which is the glued Riemannian volume (`atlasIntegral_eq`, partition of unity).
D1–D8 are inherited from `circleDiffusion` through the pointwise identities `glueΓ = Gc`, `glueL = Lc` on `𝒜₀`.
`Γ₂` and `CD(ρ,n)` are computed from the glued data.
-/

open MeasureTheory MarkovTriple.Sanity.Circle
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.Riemannian.R26

open MarkovTriple.BGL MarkovTriple.BGL.Sanity

/-- shorthand -/
noncomputable abbrev cD : DiffusionTriple 𝕋 := MarkovTriple.BGL.Sanity.circleDiffusion

lemma cD_A₀ : cD.A₀ = MarkovTriple.Sanity.Circle.A₀ := rfl

/-- the diffusion triple of the stereographic atlas -/
noncomputable def atlasDiff : DiffusionTriple 𝕋 where
  μ := μ₀
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := cD.A₀
  measurable := cD.measurable
  bounded := cD.bounded
  memLp := cD.memLp
  dense := cD.dense
  comp_mem := cD.comp_mem
  exhaustion := cD.exhaustion
  Γ := stereoAtlas.glueΓ
  L := stereoAtlas.glueL
  Γ_mem := fun f hf g hg => by
    rw [stereoAtlas_glueΓ hf hg]; exact cD.Γ_mem f hf g hg
  L_mem := fun f hf => by
    rw [stereoAtlas_glueL hf]; exact cD.L_mem f hf
  Γ_symm := fun f hf g hg => by
    rw [stereoAtlas_glueΓ hf hg, stereoAtlas_glueΓ hg hf]; exact cD.Γ_symm f hf g hg
  Γ_add := fun f hf f' hf' g hg => by
    rw [stereoAtlas_glueΓ (add_mem hf hf') hg, stereoAtlas_glueΓ hf hg, stereoAtlas_glueΓ hf' hg]
    exact cD.Γ_add f hf f' hf' g hg
  Γ_smul := fun c f hf g hg => by
    rw [stereoAtlas_glueΓ (cD.A₀.smul_mem c hf) hg, stereoAtlas_glueΓ hf hg]
    exact cD.Γ_smul c f hf g hg
  Γ_nonneg := fun f hf => by
    rw [stereoAtlas_glueΓ hf hf]; exact cD.Γ_nonneg f hf
  diffusion := fun k ψ hψ h0 f hf g hg => by
    have hc := cD.comp_mem k ψ hψ h0 f hf
    have e := cD.diffusion k ψ hψ h0 f hf g hg
    rw [stereoAtlas_glueΓ hc hg]
    simp only [stereoAtlas_glueΓ (hf _) hg]
    exact e
  ibp := fun f hf g hg => by
    rw [stereoAtlas_glueL hf, stereoAtlas_glueΓ hf hg]; exact cD.ibp f hf g hg
  integral_L := fun f hf => by
    rw [stereoAtlas_glueL hf]; exact cD.integral_L f hf


/-- on `𝒜₀` the glued `Γ` is the circle's `Γ` (the identity is false off `𝒜₀`, where both sides are junk) -/
theorem atlasDiff_Γ {f h : 𝕋 → ℝ} (hf : f ∈ MarkovTriple.Sanity.Circle.A₀)
    (hh : h ∈ MarkovTriple.Sanity.Circle.A₀) : atlasDiff.Γ f h = cD.Γ f h :=
  stereoAtlas_glueΓ hf hh

theorem atlasDiff_L {f : 𝕋 → ℝ} (hf : f ∈ MarkovTriple.Sanity.Circle.A₀) : atlasDiff.L f = cD.L f :=
  stereoAtlas_glueL hf

/-- the measure of `atlasDiff` is the Haar probability measure, which is the atlas-glued Riemannian volume -/
theorem atlasDiff_μ : atlasDiff.μ = μ₀ := rfl

/-- the formula-defined `ΓA` of the glued triple agrees with the circle's on `𝒜₀` -/
theorem atlasDiff_ΓA {f h : 𝕋 → ℝ} (hf : f ∈ MarkovTriple.Sanity.Circle.A₀)
    (hh : h ∈ MarkovTriple.Sanity.Circle.A₀) : atlasDiff.ΓA f h = cD.ΓA f h := by
  funext x
  have e1 : atlasDiff.L (f * h) = Lc (f * h) := stereoAtlas_glueL (mul_mem hf hh)
  have e2 : atlasDiff.L f = Lc f := stereoAtlas_glueL hf
  have e3 : atlasDiff.L h = Lc h := stereoAtlas_glueL hh
  simp only [DiffusionTriple.ΓA, e1, e2, e3]
  rfl

theorem atlasDiff_Γ₂ {f : 𝕋 → ℝ} (hf : f ∈ MarkovTriple.Sanity.Circle.A₀) (x : 𝕋) :
    atlasDiff.Γ₂ f f x = (stereoAtlas.glueL f x) ^ 2 := by
  have hΓ : cD.ΓA f f = Gc f f := MarkovTriple.BGL.Circle.ΓA_eq_Gc hf hf
  have hG : Gc f f ∈ MarkovTriple.Sanity.Circle.A₀ := Gc_mem hf hf
  have hLf : Lc f ∈ MarkovTriple.Sanity.Circle.A₀ := Lc_mem hf
  have e1 : atlasDiff.ΓA f f = Gc f f := (atlasDiff_ΓA hf hf).trans hΓ
  have eLf : atlasDiff.L f = Lc f := stereoAtlas_glueL hf
  have e2 : atlasDiff.ΓA f (atlasDiff.L f) = cD.ΓA f (Lc f) := by
    rw [eLf]; exact atlasDiff_ΓA hf hLf
  have e3 : atlasDiff.ΓA (atlasDiff.L f) f = cD.ΓA (Lc f) f := by
    rw [eLf]; exact atlasDiff_ΓA hLf hf
  have e4 : atlasDiff.L (Gc f f) = Lc (Gc f f) := stereoAtlas_glueL hG
  have h : cD.Γ₂ f f x = (Lc f x) ^ 2 := MarkovTriple.BGL.Circle.circle_Γ₂ hf x
  have hglue : stereoAtlas.glueL f x = Lc f x := congrFun (stereoAtlas_glueL hf) x
  rw [hglue, ← h]
  unfold DiffusionTriple.Γ₂
  rw [e1, e2, e3, e4, hΓ]
  rfl

/-- **`CD(ρ, n)` for `ρ ≤ 0`, `n ∈ [1, ∞]`, computed from the atlas-glued data** (BGL Def. 3.3.14 on `𝒜₀`). -/
theorem atlas_CD {ρ : ℝ} (hρ : ρ ≤ 0) {n : ℝ≥0∞} (hn : 1 ≤ n) {f : 𝕋 → ℝ}
    (hf : f ∈ MarkovTriple.Sanity.Circle.A₀) (x : 𝕋) :
    ρ * stereoAtlas.glueΓ f f x + (n⁻¹).toReal * (stereoAtlas.glueL f x) ^ 2 ≤ atlasDiff.Γ₂ f f x := by
  rw [atlasDiff_Γ₂ hf x, stereoAtlas_glueΓ hf hf]
  have h1 : (n⁻¹).toReal ≤ 1 := by
    have : n⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hn
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  have h2 : ρ * Gc f f x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hρ (mul_self_nonneg _)
  have h3 : (n⁻¹).toReal * (stereoAtlas.glueL f x) ^ 2 ≤ (stereoAtlas.glueL f x) ^ 2 := by
    nlinarith [sq_nonneg (stereoAtlas.glueL f x)]
  rw [stereoAtlas_glueL hf] at h3 ⊢
  linarith

end MarkovTriple.BGL.Instances.Riemannian.R26
