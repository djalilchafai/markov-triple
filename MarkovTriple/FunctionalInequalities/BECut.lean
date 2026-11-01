import Mathlib
import MarkovTriple.FunctionalInequalities.BECutoff

/-! # Bakry–Émery (Phase 4b): the cutoffs of `x log x` and `log` on `[ε, ε+M]` -/

open Filter Topology Set

namespace MarkovTriple.BE

/-- smooth compactly supported `Θ`, `Λ` with `Θ = x log x`, `Λ = log` near `[ε, ε+M]`. -/
structure Cut (ε M : ℝ) where
  Θ : ℝ → ℝ
  Λ : ℝ → ℝ
  hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ
  hΘc : HasCompactSupport Θ
  hΘeq : ∀ y ∈ Icc ε (ε + M), Θ =ᶠ[𝓝 y] fun x => x * Real.log x
  hΛ : ContDiff ℝ (⊤ : ℕ∞) Λ
  hΛc : HasCompactSupport Λ
  hΛeq : ∀ y ∈ Icc ε (ε + M), Λ =ᶠ[𝓝 y] Real.log

lemma exists_cut {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) : Nonempty (Cut ε M) := by
  have hlog : ContDiffOn ℝ (⊤ : ℕ∞) Real.log (Ioi 0) := fun x hx =>
    (Real.contDiffAt_log.2 (ne_of_gt hx)).contDiffWithinAt
  have hxlog : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => x * Real.log x) (Ioi 0) :=
    contDiffOn_id.mul hlog
  obtain ⟨Θ, h1, h2, h3⟩ := exists_cutoff hε (by linarith : ε ≤ ε + M) hxlog
  obtain ⟨Λ, h4, h5, h6⟩ := exists_cutoff hε (by linarith : ε ≤ ε + M) hlog
  exact ⟨⟨Θ, Λ, h1, h2, h3, h4, h5, h6⟩⟩

namespace Cut

variable {ε M : ℝ} (C : Cut ε M)

lemma Θ_eq {y : ℝ} (hy : y ∈ Icc ε (ε + M)) : C.Θ y = y * Real.log y := (C.hΘeq y hy).self_of_nhds

lemma Λ_eq {y : ℝ} (hy : y ∈ Icc ε (ε + M)) : C.Λ y = Real.log y := (C.hΛeq y hy).self_of_nhds

lemma deriv_Θ_eq (hε : 0 < ε) {y : ℝ} (hy : y ∈ Icc ε (ε + M)) :
    deriv C.Θ y = Real.log y + 1 := by
  have hy0 : y ≠ 0 := by linarith [hy.1]
  rw [(C.hΘeq y hy).deriv_eq]
  exact Real.deriv_mul_log hy0

lemma deriv_Λ_eq (hε : 0 < ε) {y : ℝ} (hy : y ∈ Icc ε (ε + M)) :
    deriv C.Λ y = y⁻¹ := by
  rw [(C.hΛeq y hy).deriv_eq]
  exact Real.deriv_log y

lemma deriv_deriv_Θ_eq (hε : 0 < ε) {y : ℝ} (hy : y ∈ Icc ε (ε + M)) :
    deriv (deriv C.Θ) y = y⁻¹ := by
  have hy0 : 0 < y := by linarith [hy.1]
  have h1 : deriv C.Θ =ᶠ[𝓝 y] fun x => Real.log x + 1 := by
    have h := (C.hΘeq y hy).deriv
    filter_upwards [h, Ioi_mem_nhds hy0] with x hx hx0
    rw [hx]
    exact Real.deriv_mul_log (ne_of_gt hx0)
  rw [h1.deriv_eq]
  have : HasDerivAt (fun x => Real.log x + 1) (y⁻¹) y :=
    (Real.hasDerivAt_log (ne_of_gt hy0)).add_const 1
  exact this.deriv

lemma deriv_deriv_Θ_eq' (hε : 0 < ε) {y : ℝ} (hy : y ∈ Icc ε (ε + M)) :
    deriv (deriv C.Θ) y = deriv C.Λ y := by
  rw [C.deriv_deriv_Θ_eq hε hy, C.deriv_Λ_eq hε hy]

lemma deriv_Θ_eq_Λ (hε : 0 < ε) {y : ℝ} (hy : y ∈ Icc ε (ε + M)) :
    deriv C.Θ y = C.Λ y + 1 := by
  rw [C.deriv_Θ_eq hε hy, C.Λ_eq hy]

end Cut

end MarkovTriple.BE
