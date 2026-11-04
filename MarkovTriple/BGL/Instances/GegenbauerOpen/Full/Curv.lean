import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Defs
import MarkovTriple.BGL.Instances.GegenbauerOpen.Curvature

/-!
# Curvature on the extended algebra `𝒜` (R23-G2)

`goL`, `ΓA`, `Γ₂` are local operators (they only use derivatives), so for `f ∈ 𝒜` at `x ∈ (-1,1)` they agree
with those of a globally smooth modification of `f`; `goDiff_CD` then gives the pointwise inequality of
`FullTriple.CD` for all `f ∈ 𝒜`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

lemma goL_ev {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) : goL f =ᶠ[𝓝 x] goL g := by
  filter_upwards [h.eventually_nhds] with y (hy : f =ᶠ[𝓝 y] g)
  simp only [goL, hy.deriv_eq, hy.deriv.deriv_eq]

lemma goΓA_ev {f g f' g' : ℝ → ℝ} {x : ℝ} (hf : f =ᶠ[𝓝 x] f') (hg : g =ᶠ[𝓝 x] g') :
    goDiff.ΓA f g =ᶠ[𝓝 x] goDiff.ΓA f' g' := by
  have hm : f * g =ᶠ[𝓝 x] f' * g' := hf.mul hg
  have h1 := goL_ev hm
  have h2 := goL_ev hg
  have h3 := goL_ev hf
  filter_upwards [h1, h2, h3, hf.eventually_nhds, hg.eventually_nhds] with y a b c (d : f =ᶠ[𝓝 y] f') (e : g =ᶠ[𝓝 y] g')
  have hfy : f y = f' y := d.eq_of_nhds
  have hgy : g y = g' y := e.eq_of_nhds
  show (goL (f * g) y - f y * goL g y - g y * goL f y) / 2 =
    (goL (f' * g') y - f' y * goL g' y - g' y * goL f' y) / 2
  rw [a, b, c, hfy, hgy]

lemma goΓ₂_local {f f' : ℝ → ℝ} {x : ℝ} (hf : f =ᶠ[𝓝 x] f') :
    goDiff.Γ₂ f f x = goDiff.Γ₂ f' f' x := by
  have hL := goL_ev hf
  have hG := goΓA_ev hf hf
  have e1 : goL (goDiff.ΓA f f) x = goL (goDiff.ΓA f' f') x := (goL_ev hG).eq_of_nhds
  have e2 : goDiff.ΓA f (goL f) x = goDiff.ΓA f' (goL f') x := (goΓA_ev hf hL).eq_of_nhds
  have e3 : goDiff.ΓA (goL f) f x = goDiff.ΓA (goL f') f' x := (goΓA_ev hL hf).eq_of_nhds
  show (goL (goDiff.ΓA f f) x - goDiff.ΓA f (goL f) x - goDiff.ΓA (goL f) f x) / 2 =
    (goL (goDiff.ΓA f' f') x - goDiff.ΓA f' (goL f') x - goDiff.ΓA (goL f') f' x) / 2
  rw [e1, e2, e3]

/-- **`CD(ρ,n)` pointwise on `(-1,1)` for every `f ∈ 𝒜`** (the shape of `FullTriple.CD`). -/
theorem goA_CD {ρ : ℝ} {n : ℝ≥0∞} (hρ : ρ ≤ 3) (hn : 4 ≤ n) {f : ℝ → ℝ} (hf : f ∈ goA) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, ρ * goDiff.ΓA f f x + (n⁻¹).toReal * (goDiff.L f x) ^ 2 ≤
      goDiff.Γ₂ f f x := by
  intro x hx
  obtain ⟨g, hg, hfg⟩ := exists_smooth_agree_at hf.2 hx
  have h := (goDiff_CD hρ hn).2 g hg x hx
  have e1 : goDiff.ΓA f f x = goDiff.ΓA g g x := (goΓA_ev hfg hfg).eq_of_nhds
  have e2 : goDiff.L f x = goDiff.L g x := (goL_ev hfg).eq_of_nhds
  rw [e1, e2, goΓ₂_local hfg]
  exact h

end MarkovTriple.BGL.Instances.GegenbauerOpen
