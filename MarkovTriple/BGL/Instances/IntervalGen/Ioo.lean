import Mathlib
import MarkovTriple.BGL.Instances.IntervalGen.NotComplete
import MarkovTriple.BGL.Instances.IntervalGen.NotESA

/-!
# Bounded intervals `(a,b)` (G5): specialisations of G1-G4 to `Ω = (a,b)`

See `STATEMENTS_R22_E1.md`.  `(0,1)` recovers the Round 21 measure `Interval.ivμ`.
-/

open MeasureTheory Set

namespace MarkovTriple.BGL.Instances.IntervalGen

/-- the diffusion triple `((a,b), (b-a)⁻¹ dx, C_c^∞((a,b)))`. -/
@[reducible] noncomputable def iooDiff (a b : ℝ) (h : a < b) : MarkovTriple.BGL.DiffusionTriple ℝ :=
  (BddOpen.Ioo a b h).diff

theorem BddOpen.Ioo_zero_one_μ (h : (0 : ℝ) < 1) : (BddOpen.Ioo 0 1 h).μ = Interval.ivμ := by
  show ((volume (Set.Ioo (0 : ℝ) 1))⁻¹ • volume.restrict (Set.Ioo (0 : ℝ) 1)) =
    volume.restrict (Set.Ioo (0 : ℝ) 1)
  simp [Real.volume_Ioo]

theorem Ioo_Γ₂_eq (a b : ℝ) (h : a < b) {f : ℝ → ℝ} (hf : Lebesgue.Sm f) (x : ℝ) :
    (iooDiff a b h).Γ₂ f f x = (deriv (deriv f) x) ^ 2 :=
  (BddOpen.Ioo a b h).Γ₂_eq hf x

theorem Ioo_diff_CD (a b : ℝ) (h : a < b) {ρ : ℝ} {n : ENNReal} (hρ : ρ ≤ 0) (hn : 1 ≤ n) :
    (BddOpen.Ioo a b h).GenCD ρ n :=
  (BddOpen.Ioo a b h).diff_CD hρ hn

theorem Ioo_not_complete (a b : ℝ) (h : a < b) : ¬ (iooDiff a b h).IsComplete :=
  (BddOpen.Ioo a b h).not_complete

theorem Ioo_not_esaProp (a b : ℝ) (h : a < b) : ¬ (iooDiff a b h).ESAProp :=
  (BddOpen.Ioo a b h).not_esaProp

theorem Ioo_no_fullTriple (a b : ℝ) (h : a < b) (T : MarkovTriple.BGL.FullTriple ℝ) :
    T.toDiffusionTriple ≠ iooDiff a b h :=
  (BddOpen.Ioo a b h).no_fullTriple T

end MarkovTriple.BGL.Instances.IntervalGen
