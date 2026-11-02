import Mathlib

/-! # Bakry–Émery (Phase 4b): smooth compactly supported modifications -/

open Filter Topology Set

namespace MarkovTriple.BE

/-- A smooth compactly supported function that coincides with `g` (smooth on `(0,∞)`) near every
point of `[α, β] ⊂ (0,∞)`. -/
lemma exists_cutoff {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioi 0)) :
    ∃ Θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Θ ∧ HasCompactSupport Θ ∧
      ∀ y ∈ Icc α β, Θ =ᶠ[𝓝 y] g := by
  let b : ContDiffBump (β : ℝ) :=
    ⟨β - α / 2, β - α / 4, by linarith, by linarith⟩
  refine ⟨fun y => b y * g y, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : 0 < y
    · exact (b.contDiff.contDiffAt).mul
        ((hg.contDiffAt (Ioi_mem_nhds hy)))
    · have h1 : ∀ᶠ y' in 𝓝 y, (fun y => b y * g y) y' = 0 := by
        have : Iio (α / 4) ∈ 𝓝 y := Iio_mem_nhds (by linarith [not_lt.mp hy])
        filter_upwards [this] with y' hy'
        have : b y' = 0 := by
          rw [← Function.notMem_support, b.support_eq, Metric.mem_ball, Real.dist_eq]
          intro h
          have hr : b.rOut = β - α / 4 := rfl
          have := abs_lt.mp h
          simp only [mem_Iio] at hy'
          rw [hr] at this
          linarith [this.1]
        simp [this]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h1
  · exact b.hasCompactSupport.mul_right
  · intro y hy
    have hmem : y ∈ Metric.ball β (β - α / 2) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    have hr : b.rIn = β - α / 2 := rfl
    rw [← hr] at hmem
    filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with y' hy'
    have := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy')
    simp [this]

/-- bounds for a smooth compactly supported function and its first three derivatives -/
lemma exists_bounds {Θ : ℝ → ℝ} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) (hc : HasCompactSupport Θ) :
    ∃ K : ℝ, ∀ x, |Θ x| ≤ K ∧ |deriv Θ x| ≤ K ∧ |deriv (deriv Θ) x| ≤ K ∧
      |deriv (deriv (deriv Θ)) x| ≤ K := by
  have d1 : ContDiff ℝ (⊤ : ℕ∞) (deriv Θ) := (contDiff_infty_iff_deriv.1 hΘ).2
  have d2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv Θ)) := (contDiff_infty_iff_deriv.1 d1).2
  have d3 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (deriv Θ))) := (contDiff_infty_iff_deriv.1 d2).2
  have c1 : HasCompactSupport (deriv Θ) := hc.deriv
  have c2 : HasCompactSupport (deriv (deriv Θ)) := c1.deriv
  have c3 : HasCompactSupport (deriv (deriv (deriv Θ))) := c2.deriv
  obtain ⟨K0, h0⟩ := hΘ.continuous.bounded_above_of_compact_support hc
  obtain ⟨K1, h1⟩ := d1.continuous.bounded_above_of_compact_support c1
  obtain ⟨K2, h2⟩ := d2.continuous.bounded_above_of_compact_support c2
  obtain ⟨K3, h3⟩ := d3.continuous.bounded_above_of_compact_support c3
  refine ⟨max (max K0 K1) (max K2 K3), fun x => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (by simpa using h0 x : |Θ x| ≤ K0).trans (by simp)
  · exact (by simpa using h1 x : |deriv Θ x| ≤ K1).trans (by simp)
  · exact (by simpa using h2 x : |deriv (deriv Θ) x| ≤ K2).trans (by simp)
  · exact (by simpa using h3 x : |deriv (deriv (deriv Θ)) x| ≤ K3).trans (by simp)

end MarkovTriple.BE
