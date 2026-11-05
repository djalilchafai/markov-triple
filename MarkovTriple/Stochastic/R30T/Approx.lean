import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Calculus

/-!
# Round 30 (T), part 1: uniform approximation of `C_c(ℝ^d)` by `C_c^∞(ℝ^d)`

Real analysis (Mathlib's `UniformContinuous.exists_contDiff_dist_le` + a smooth cut-off), used to extend the
continuity of `P_t f` from `f ∈ C_c^∞` to `f ∈ C_c`.
-/

open MeasureTheory Filter Topology Set
open scoped CompactlySupported ContDiff

namespace MarkovTriple.Stochastic.R30T

open MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

/-- a smooth cut-off equal to `1` on a compact set `K`, with values in `[0,1]` and compact support. -/
lemma exists_cutoff_cs {K : Set (Rd d)} (hK : IsCompact K) :
    ∃ χ : Rd d → ℝ, Sm χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hs : IsClosed ((Metric.ball (0 : Rd d) (R + 1))ᶜ) := Metric.isOpen_ball.isClosed_compl
  have hd : Disjoint ((Metric.ball (0 : Rd d) (R + 1))ᶜ) K := by
    rw [Set.disjoint_left]
    intro x hx hxK
    apply hx
    have := hR hxK
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at this
    linarith
  obtain ⟨χ, hχ, hrange, hs0, hK1⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hs hK.isClosed hd
  refine ⟨χ, hχ, ?_, fun x => hrange ⟨x, rfl⟩, fun x hx => (hK1 x).1 hx⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Rd d) (R + 1)) ?_
  intro x hx
  by_contra hxc
  apply hx
  rw [← hs0]
  intro hb
  exact hxc (Metric.mem_closedBall.2 (le_of_lt (by simpa using hb)))

/-- `C_c` functions are uniform limits of `C_c^∞` functions. -/
lemma exists_A₀_approx (f : C_c(Rd d, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h ∈ A₀ d, ∀ x, |h x - f x| < ε := by
  have huc : UniformContinuous (f : Rd d → ℝ) := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  obtain ⟨g, hg, hgf⟩ := huc.exists_contDiff_dist_le hε
  obtain ⟨χ, hχ, hχc, hχ01, hχ1⟩ := exists_cutoff_cs (d := d) f.hasCompactSupport
  refine ⟨fun x => χ x * g x, ⟨hχ.mul hg, hχc.mul_right⟩, fun x => ?_⟩
  show |χ x * g x - f x| < ε
  by_cases hx : x ∈ tsupport (f : Rd d → ℝ)
  · rw [hχ1 x hx, one_mul]
    simpa [Real.dist_eq] using hgf x
  · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    have := hgf x
    rw [Real.dist_eq, h0, sub_zero] at this
    rw [h0, sub_zero, abs_mul, abs_of_nonneg (hχ01 x).1]
    calc χ x * |g x| ≤ 1 * |g x| := mul_le_mul_of_nonneg_right (hχ01 x).2 (abs_nonneg _)
      _ < ε := by simpa using this

end MarkovTriple.Stochastic.R30T
