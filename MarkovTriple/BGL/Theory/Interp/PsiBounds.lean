import Mathlib
import MarkovTriple.BGL.Theory.Strong.Psi

/-!
# Elementary estimates for `ψ_ε(r) = √(r+ε²) - ε` on `[0,∞)` (inputs of the Nemytskii lemma `hasDerivAt_pair`)
-/

open Set

namespace MarkovTriple.BGL

section

variable {ε : ℝ}

private lemma S_facts (hε : 0 < ε) {a : ℝ} (ha : 0 ≤ a) :
    ε ≤ Real.sqrt (a + ε ^ 2) ∧ Real.sqrt (a + ε ^ 2) ^ 2 = a + ε ^ 2 := by
  have hp : 0 ≤ a + ε ^ 2 := by positivity
  refine ⟨Real.le_sqrt_of_sq_le (by nlinarith), Real.sq_sqrt hp⟩

/-- `(ψ(b) - ψ(a))² ≤ |b - a|`. -/
lemma psiS_hH (hε : 0 < ε) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (psiS ε b - psiS ε a) ^ 2 ≤ |b - a| := by
  rw [psiS_eq hε (by nlinarith [sq_nonneg ε]), psiS_eq hε (by nlinarith [sq_nonneg ε])]
  obtain ⟨hSa, hSa2⟩ := S_facts hε ha
  obtain ⟨hSb, hSb2⟩ := S_facts hε hb
  set Sa := Real.sqrt (a + ε ^ 2)
  set Sb := Real.sqrt (b + ε ^ 2)
  have : b - a = (Sb - Sa) * (Sb + Sa) := by nlinarith
  rw [this, abs_mul, abs_of_pos (by linarith : 0 < Sb + Sa)]
  have h1 : (Sb - Sa - 0) ^ 2 = |Sb - Sa| * |Sb - Sa| := by rw [sub_zero, ← sq, sq_abs]
  have e : Sb - ε - (Sa - ε) = Sb - Sa := by ring
  rw [e]
  have h2 : |Sb - Sa| ≤ Sb + Sa := by rw [abs_le]; constructor <;> linarith
  calc (Sb - Sa) ^ 2 = |Sb - Sa| * |Sb - Sa| := by rw [← sq, sq_abs]
    _ ≤ |Sb - Sa| * (Sb + Sa) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

lemma psiS_deriv_bound (hε : 0 < ε) {a : ℝ} (ha : 0 ≤ a) : |deriv (psiS ε) a| ≤ 1 / (2 * ε) := by
  rw [deriv_psiS hε ha]
  obtain ⟨hSa, -⟩ := S_facts hε ha
  rw [abs_of_pos (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- remainder estimate. -/
lemma psiS_rem (hε : 0 < ε) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |psiS ε b - psiS ε a - deriv (psiS ε) a * (b - a)| ≤
      |b - a| * min (1 / (8 * ε ^ 3) * |b - a|) (2 * (1 / (2 * ε))) := by
  rw [deriv_psiS hε ha, psiS_eq hε (by nlinarith [sq_nonneg ε]), psiS_eq hε (by nlinarith [sq_nonneg ε])]
  obtain ⟨hSa, hSa2⟩ := S_facts hε ha
  obtain ⟨hSb, hSb2⟩ := S_facts hε hb
  set Sa := Real.sqrt (a + ε ^ 2)
  set Sb := Real.sqrt (b + ε ^ 2)
  have hSa0 : 0 < Sa := by linarith
  have hba : b - a = (Sb - Sa) * (Sb + Sa) := by nlinarith
  have hR : Sb - ε - (Sa - ε) - 1 / (2 * Sa) * (b - a) = -((Sb - Sa) ^ 2 / (2 * Sa)) := by
    rw [hba]; field_simp; ring
  rw [hR, abs_neg, abs_of_nonneg (by positivity)]
  have hsum : 0 < Sb + Sa := by linarith
  have habs : |b - a| = |Sb - Sa| * (Sb + Sa) := by rw [hba, abs_mul, abs_of_pos hsum]
  have hd2 : (Sb - Sa) ^ 2 * (Sb + Sa) ^ 2 = |b - a| ^ 2 := by
    rw [sq_abs, hba]; ring
  rw [mul_min_of_nonneg _ _ (abs_nonneg (b - a))]
  apply le_min
  · -- (Sb-Sa)^2/(2 Sa) ≤ |b-a| * (1/(8 ε³) |b-a|)
    have h4 : 4 * ε ^ 2 ≤ (Sb + Sa) ^ 2 := by nlinarith
    have h5 : (Sb - Sa) ^ 2 * (4 * ε ^ 2) ≤ |b - a| ^ 2 := by
      rw [← hd2]; exact mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
    rw [div_le_iff₀ (by positivity)]
    have h6 : |b - a| * (1 / (8 * ε ^ 3) * |b - a|) * (2 * Sa) =
        |b - a| ^ 2 * (Sa / (4 * ε ^ 3)) := by field_simp; ring
    rw [h6]
    have h7 : 1 ≤ Sa / ε := by rw [le_div_iff₀ hε]; linarith
    have h8 : (Sb - Sa) ^ 2 ≤ |b - a| ^ 2 / (4 * ε ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; exact h5
    have h9 : |b - a| ^ 2 / (4 * ε ^ 2) ≤ |b - a| ^ 2 * (Sa / (4 * ε ^ 3)) := by
      have : |b - a| ^ 2 * (Sa / (4 * ε ^ 3)) = |b - a| ^ 2 / (4 * ε ^ 2) * (Sa / ε) := by
        field_simp
      rw [this]
      exact le_mul_of_one_le_right (by positivity) h7
    linarith
  · -- (Sb-Sa)^2/(2 Sa) ≤ |b-a| * (2 * (1/(2ε)))
    rw [div_le_iff₀ (by positivity)]
    have h1 : (Sb - Sa) ^ 2 ≤ |b - a| := by
      have h2 : |Sb - Sa| ≤ Sb + Sa := by rw [abs_le]; constructor <;> linarith
      calc (Sb - Sa) ^ 2 = |Sb - Sa| * |Sb - Sa| := by rw [← sq, sq_abs]
        _ ≤ |Sb - Sa| * (Sb + Sa) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |b - a| := habs.symm
    have h3 : |b - a| * (2 * (1 / (2 * ε))) * (2 * Sa) = |b - a| * (2 * Sa / ε) := by
      field_simp
    rw [h3]
    have h7 : 1 ≤ 2 * Sa / ε := by rw [le_div_iff₀ hε]; linarith
    calc (Sb - Sa) ^ 2 ≤ |b - a| := h1
      _ = |b - a| * 1 := by ring
      _ ≤ |b - a| * (2 * Sa / ε) := mul_le_mul_of_nonneg_left h7 (abs_nonneg _)

lemma psiS_measurable (hε : 0 < ε) : Measurable (psiS ε) := (psiS_smooth hε).continuous.measurable

lemma deriv_psiS_measurable (hε : 0 < ε) : Measurable (deriv (psiS ε)) :=
  ((contDiff_infty_iff_deriv.1 (psiS_smooth hε)).2).continuous.measurable

end

end MarkovTriple.BGL
