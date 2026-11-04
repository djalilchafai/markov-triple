import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDefs

/-!
# Heat flow on `ℝ^d`: pointwise, smoothness, `L²` facts (Round 24, stream A, STATEMENTS_R24_A.md, part H-a)

STUB (statements fixed; proofs `sorry` until stream H-a delivers).  Port of `Instances/Lebesgue/Heat.lean` to `ℝ^d`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ ψ : (Fin d → ℝ) → ℝ}

theorem heatRd_zero (φ : (Fin d → ℝ) → ℝ) : heatRd 0 φ = φ := by
  funext x; simp [heatRd]

theorem heatRd_smooth (hφ : φ ∈ A₀ d) (a : ℝ) : Sm (heatRd a φ) := sorry

theorem dd_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) (i : Fin d) : dd i (heatRd a φ) = heatRd a (dd i φ) := sorry

theorem Lf_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) : Lf (heatRd a φ) = heatRd a (Lf φ) := sorry

theorem abs_heatRd_le {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (a : ℝ) (x : Fin d → ℝ) : |heatRd a φ x| ≤ C := sorry

theorem integrable_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) : Integrable (heatRd a φ) volume := sorry

theorem memLp_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) : MemLp (heatRd a φ) 2 volume := sorry

theorem integral_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) : ∫ x, heatRd a φ x = ∫ x, φ x := sorry

theorem coeFn_heatL2 (hφ : φ ∈ A₀ d) (a : ℝ) :
    (heatL2 φ a : (Fin d → ℝ) → ℝ) =ᵐ[volume] heatRd a φ := sorry

/-- `heatL2 φ 0` is the `L²` class of `φ`. -/
theorem heatL2_zero (hφ : φ ∈ A₀ d) : heatL2 φ 0 = (memLp_of hφ 2).toLp φ := sorry

/-- symmetry of Gaussian smoothing. -/
theorem integral_mul_heatRd_comm (hφ : φ ∈ A₀ d) (hψ : ψ ∈ A₀ d) (a : ℝ) :
    ∫ x, ψ x * heatRd a φ x = ∫ x, φ x * heatRd a ψ x := sorry

/-- contraction in `L²` (Jensen + translation invariance). -/
theorem norm_heatL2_le (hφ : φ ∈ A₀ d) (a : ℝ) : ‖heatL2 φ a‖ ≤ ‖heatL2 φ 0‖ := sorry

/-- `S11` ingredient: `heatRd a (uₙ) → 1` pointwise for `a ≠ 0` if `uₙ → 1` a.e. with `|uₙ| ≤ 1` a.e. -/
theorem heatRd_tendsto_one {a : ℝ} (ha : a ≠ 0) {u : ℕ → (Fin d → ℝ) → ℝ} (hmeas : ∀ n, Measurable (u n))
    (hle : ∀ n, ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), |u n y| ≤ 1)
    (hlim : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), Tendsto (fun n => u n y) atTop (𝓝 1))
    (x : Fin d → ℝ) : Tendsto (fun n => heatRd a (u n) x) atTop (𝓝 1) := sorry

/-- `S10` ingredient: the smoothed test function tends to `0` in `L²` as the scale `a → ∞`
(`|heatRd a φ| ≤ ‖φ‖₁ (2π a²)^{-d/2}`). -/
theorem tendsto_heatL2_zero (hφ : φ ∈ A₀ d) (hd : 1 ≤ d) :
    Tendsto (fun a : ℝ => heatL2 φ a) atTop (𝓝 0) := sorry

end MarkovTriple.BGL.LebesgueRd
