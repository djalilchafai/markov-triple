import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.HypExample
import MarkovTriple.BGL.Instances.Riemannian.Unconditional

/-!
# Unconditional functional inequalities on the weighted hyperbolic plane (round 17)

`hypRiem` (`HypExample.lean`) satisfies `Curv 1` (`Ric + ∇∇W = (2 cosh d − 1) g ≥ g`); `WeakHypo` and `F8` hold for every
`EllData` (round 16), so Poincaré, spectral gap, `L²` decay, `CD(1,∞)`, log-Sobolev `LS(1,0)` and the gradient bound hold for the
weighted hyperbolic plane, whose co-metric `e^{2t} dx² ⊕ 1` is unbounded.  `hypRiem_not_curv_gt`: `Curv ρ` fails for `ρ > 1`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (DiffusionTriple FullTriple HasGradientBound)

/-- the co-metric of `hypRiem` is NOT bounded above: the round-15/16 hypothesis (`g_bdd`) fails, the new `g_exh` is needed -/
theorem hypRiem_g_unbounded : ¬ ∃ Λ : ℝ, ∀ (x v : Rd 2),
    ∑ i, ∑ j, hypRiem.g i j x * v i * v j ≤ Λ * ∑ i, v i ^ 2 := by
  rintro ⟨Λ, h⟩
  have h1 := h (fun i => if i = 0 then 0 else |Λ| + 1) (fun i => if i = 0 then 1 else 0)
  have h2 := Real.add_one_le_exp (2 * (|Λ| + 1))
  have h3 := le_abs_self Λ
  have h4 := abs_nonneg Λ
  simp [hypRiem.g_eq, Hyp.G, Hyp.E] at h1
  linarith

theorem hypRiem_not_curv_gt {ρ : ℝ} (hρ : 1 < ρ) : ¬ hypRiem.Curv ρ :=
  fun h => absurd (hypRiem.curv_iff.1 h) (not_le.2 hρ)

theorem hypRiem_poincare : hypRiem.riemDiff.PI 1 := by
  have := hypRiem.riem_poincare_unconditional (ρ := 1) one_pos hypRiem.curv
  simpa using this

theorem hypRiem_spectralGap : (DiffusionTriple.formData hypRiem.riemDiff).HasSpectralGap 1 :=
  hypRiem.riem_spectralGap_unconditional one_pos hypRiem.curv

theorem hypRiem_expDecay : (DiffusionTriple.formData hypRiem.riemDiff).HasExpDecay 1 :=
  hypRiem.riem_expDecay_unconditional one_pos hypRiem.curv

theorem hypRiem_CD : hypRiem.riemFull_unconditional.CD 1 ∞ :=
  hypRiem.riemFull_CD_unconditional hypRiem.curv

theorem hypRiem_logSobolev : hypRiem.riemFull_unconditional.toDiffusionTriple.LS 1 0 := by
  have := hypRiem.riemFull_logSobolev_unconditional (ρ := 1) one_pos hypRiem.curv
  simpa using this

theorem hypRiem_hasGradientBound :
    HasGradientBound hypRiem.riemFull_unconditional.toDiffusionTriple hypRiem.riemFull_unconditional.A 1 :=
  hypRiem.riemFull_hasGradientBound_unconditional zero_le_one hypRiem.curv

end MarkovTriple.BGL.Instances.Riemannian
