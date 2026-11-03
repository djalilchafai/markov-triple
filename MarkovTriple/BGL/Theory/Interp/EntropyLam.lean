import Mathlib
import MarkovTriple.BGL.Theory.Interp.EntropyAnalysis
import MarkovTriple.BGL.Analysis.BE.Cut

/-!
# The shifted cutoffs `λ_k(y) = Λ^{(k)}(ε + y)` of `log` on `[ε, ε+M]` (`y ∈ [0,M]` is the range of `P_s φ`)

On `y ∈ [0,M]`: `λ₁ = 1/(ε+y)`, `λ₂ = -λ₁²`, `λ₃ = 2λ₁³ = -2λ₁λ₂`, `(ε+y) λ₁ = 1`.  All four are `C^∞`, bounded,
with `deriv λ_k = λ_{k+1}`.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL

variable {ε M : ℝ}

/-- `λ₀(y) = Λ(ε+y)`. -/
noncomputable def lam0 (C : BE.Cut ε M) (y : ℝ) : ℝ := C.Λ (ε + y)
/-- `λ₁(y) = Λ'(ε+y)`. -/
noncomputable def lam1 (C : BE.Cut ε M) (y : ℝ) : ℝ := deriv C.Λ (ε + y)
/-- `λ₂(y) = Λ''(ε+y)`. -/
noncomputable def lam2 (C : BE.Cut ε M) (y : ℝ) : ℝ := deriv (deriv C.Λ) (ε + y)
/-- `λ₃(y) = Λ'''(ε+y)`. -/
noncomputable def lam3 (C : BE.Cut ε M) (y : ℝ) : ℝ := deriv (deriv (deriv C.Λ)) (ε + y)

namespace Lam

variable (C : BE.Cut ε M)

lemma smooth0 : ContDiff ℝ (⊤ : ℕ∞) (lam0 C) := C.hΛ.comp (contDiff_const.add contDiff_id)

lemma smooth1 : ContDiff ℝ (⊤ : ℕ∞) (lam1 C) :=
  (contDiff_infty_iff_deriv.1 C.hΛ).2.comp (contDiff_const.add contDiff_id)

lemma smooth2 : ContDiff ℝ (⊤ : ℕ∞) (lam2 C) :=
  (contDiff_infty_iff_deriv.1 (contDiff_infty_iff_deriv.1 C.hΛ).2).2.comp
    (contDiff_const.add contDiff_id)

lemma smooth3 : ContDiff ℝ (⊤ : ℕ∞) (lam3 C) :=
  (contDiff_infty_iff_deriv.1 (contDiff_infty_iff_deriv.1
    (contDiff_infty_iff_deriv.1 C.hΛ).2).2).2.comp (contDiff_const.add contDiff_id)

lemma deriv0 : deriv (lam0 C) = lam1 C := by
  funext y; simp only [lam1]; exact deriv_comp_const_add C.Λ ε y

lemma deriv1 : deriv (lam1 C) = lam2 C := by
  funext y; simp only [lam2]; exact deriv_comp_const_add (deriv C.Λ) ε y

lemma deriv2 : deriv (lam2 C) = lam3 C := by
  funext y; simp only [lam3]; exact deriv_comp_const_add (deriv (deriv C.Λ)) ε y

/-- uniform bounds `|λ_k| ≤ K`. -/
lemma bounds : ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |lam0 C y| ≤ K ∧ |lam1 C y| ≤ K ∧ |lam2 C y| ≤ K ∧ |lam3 C y| ≤ K := by
  have h1 := (contDiff_infty_iff_deriv.1 C.hΛ).2
  have h2 := (contDiff_infty_iff_deriv.1 h1).2
  obtain ⟨K1, -, hK1, -, hb0, hb1, -, -⟩ := cs_facts C.hΛ C.hΛc
  obtain ⟨K2, -, hK2, -, hc1, hc2, -, -⟩ := cs_facts h1 C.hΛc.deriv
  obtain ⟨K3, -, hK3, -, hd2, hd3, -, -⟩ := cs_facts h2 C.hΛc.deriv.deriv
  refine ⟨max (max K1 K2) K3, le_max_of_le_left (le_max_of_le_left hK1), fun y => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (hb0 _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hb1 _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hc2 _).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hd3 _).trans (le_max_right _ _)

/-- values on the range: `λ₁ = (ε+y)⁻¹`, `λ₂ = -(λ₁)²`, `λ₃ = -2 λ₁ λ₂`. -/
lemma values {y : ℝ} (hy : y ∈ Icc (0 : ℝ) M) (hε : 0 < ε) :
    lam1 C y = (ε + y)⁻¹ ∧ lam2 C y = -(lam1 C y) ^ 2 ∧ lam3 C y = -2 * lam1 C y * lam2 C y := by
  have hy' : ε + y ∈ Icc ε (ε + M) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hpos : 0 < ε + y := by linarith [hy.1]
  have e1 : deriv C.Λ =ᶠ[𝓝 (ε + y)] fun x => x⁻¹ := by
    have := (C.hΛeq (ε + y) hy').deriv
    rw [Real.deriv_log'] at this
    exact this
  have e2 : deriv (deriv C.Λ) =ᶠ[𝓝 (ε + y)] fun x => -(x ^ 2)⁻¹ := by
    have := e1.deriv
    have hd : deriv (fun x : ℝ => x⁻¹) = fun x => -(x ^ 2)⁻¹ := funext fun x => deriv_inv (x := x)
    rw [hd] at this
    exact this
  have v1 : lam1 C y = (ε + y)⁻¹ := by simp only [lam1]; exact e1.self_of_nhds
  have v2 : lam2 C y = -((ε + y) ^ 2)⁻¹ := by simp only [lam2]; exact e2.self_of_nhds
  have v3 : lam3 C y = 2 * ((ε + y) ^ 3)⁻¹ := by
    simp only [lam3]
    rw [e2.deriv_eq]
    have hne : ε + y ≠ 0 := hpos.ne'
    have h : HasDerivAt (fun x : ℝ => -(x ^ 2)⁻¹) (2 * (ε + y) / ((ε + y) ^ 2) ^ 2) (ε + y) := by
      have := ((hasDerivAt_pow 2 (ε + y)).inv (pow_ne_zero 2 hne)).neg
      convert this using 1
      field_simp
      simp
    rw [h.deriv]
    field_simp
  refine ⟨v1, ?_, ?_⟩
  · rw [v2, v1, inv_pow]
  · rw [v3, v2, v1]
    field_simp

end Lam

end MarkovTriple.BGL
