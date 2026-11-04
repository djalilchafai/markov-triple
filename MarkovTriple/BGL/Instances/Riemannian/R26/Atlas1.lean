import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R26.Chart1

/-!
# One-dimensional atlases of the circle and glued `Γ`, `L`

An atlas is a family of charts whose images cover `𝕋`.  The glued `Γ(f,h)(p)`, `L f (p)` are the chartwise values computed
in a chart containing `p` (chosen by `Classical.choose`); by `chart_transition` the value does not depend on the choice
(`glueΓ_indep`, `glueL_indep`), and they equal the intrinsic `Gc`, `Lc` on `𝒜₀`.
-/

open MarkovTriple.Sanity.Circle
open scoped Real

namespace MarkovTriple.BGL.Instances.Riemannian.R26

structure Atlas1 where
  ι : Type
  chart : ι → Chart1
  cover : ∀ p : 𝕋, ∃ i t, (chart i).pt t = p

namespace Atlas1
variable (A : Atlas1)

/-- chart index chosen at `p` -/
noncomputable def idx (p : 𝕋) : A.ι := (A.cover p).choose
/-- coordinate chosen at `p` -/
noncomputable def pos (p : 𝕋) : ℝ := (A.cover p).choose_spec.choose
lemma pos_spec (p : 𝕋) : (A.chart (A.idx p)).pt (A.pos p) = p := (A.cover p).choose_spec.choose_spec

/-- glued carré du champ -/
noncomputable def glueΓ (f h : 𝕋 → ℝ) (p : 𝕋) : ℝ := (A.chart (A.idx p)).Γ f h (A.pos p)
/-- glued Laplace–Beltrami operator -/
noncomputable def glueL (f : 𝕋 → ℝ) (p : 𝕋) : ℝ := (A.chart (A.idx p)).L f (A.pos p)

theorem glueΓ_eq {f h : 𝕋 → ℝ} (hf : f ∈ A₀) (hh : h ∈ A₀) : A.glueΓ f h = Gc f h := by
  funext p
  rw [glueΓ, Chart1.Γ_eq _ hf hh, A.pos_spec]

theorem glueL_eq {f : 𝕋 → ℝ} (hf : f ∈ A₀) : A.glueL f = Lc f := by
  funext p
  rw [glueL, Chart1.L_eq _ hf, A.pos_spec]

/-- the glued value may be computed in ANY chart containing `p` -/
theorem glueΓ_indep {f h : 𝕋 → ℝ} (hf : f ∈ A₀) (hh : h ∈ A₀) (i : A.ι) (t : ℝ) {p : 𝕋}
    (hp : (A.chart i).pt t = p) : A.glueΓ f h p = (A.chart i).Γ f h t :=
  (Chart1.chart_transition _ _ ((A.pos_spec p).trans hp.symm) hf hh).1

theorem glueL_indep {f : 𝕋 → ℝ} (hf : f ∈ A₀) (i : A.ι) (t : ℝ) {p : 𝕋}
    (hp : (A.chart i).pt t = p) : A.glueL f p = (A.chart i).L f t :=
  (Chart1.chart_transition _ _ ((A.pos_spec p).trans hp.symm) hf hf).2

end Atlas1

/-- the stereographic atlas (`Bool`: `true` = north, `false` = south) -/
noncomputable def stereoAtlas : Atlas1 where
  ι := Bool
  chart := fun b => if b then northChart else southChart
  cover := fun p => by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective p
    have hπ : 0 < π := Real.pi_pos
    have h0 := Int.fract_nonneg y
    have h1 := Int.fract_lt_one y
    have hy : (y : 𝕋) = ((Int.fract y : ℝ) : 𝕋) := by
      have : y = Int.fract y + (⌊y⌋ : ℤ) := by rw [Int.fract]; ring
      conv_lhs => rw [this]
      rw [AddCircle.coe_add]
      have : ((⌊y⌋ : ℝ) : 𝕋) = 0 := by
        have := AddCircle.coe_period (1 : ℝ)
        rw [show ((⌊y⌋ : ℤ) : ℝ) = ⌊y⌋ • (1 : ℝ) by simp, AddCircle.coe_zsmul, this]
        simp
      rw [this, add_zero]
    rcases eq_or_lt_of_le h0 with h | h
    · refine ⟨true, 0, ?_⟩
      rw [hy, ← h]
      simp [Chart1.pt, northChart]
    · refine ⟨false, Real.tan (π * (Int.fract y - 1 / 2)), ?_⟩
      rw [hy]
      simp only [Bool.false_eq_true, ↓reduceIte, Chart1.pt, southChart]
      rw [Real.arctan_tan (by nlinarith) (by nlinarith)]
      congr 1
      field_simp; ring

theorem stereoAtlas_glueΓ {f h : 𝕋 → ℝ} (hf : f ∈ A₀) (hh : h ∈ A₀) : stereoAtlas.glueΓ f h = Gc f h :=
  stereoAtlas.glueΓ_eq hf hh

theorem stereoAtlas_glueL {f : 𝕋 → ℝ} (hf : f ∈ A₀) : stereoAtlas.glueL f = Lc f :=
  stereoAtlas.glueL_eq hf

end MarkovTriple.BGL.Instances.Riemannian.R26
