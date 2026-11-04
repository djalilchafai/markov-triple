import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.HypExample
import MarkovTriple.BGL.Instances.Riemannian.Core2RiemMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllRadialMain

/-!
# Round 22 (E4), part H: the radial-jet route to `CoreCut` fails for the hyperbolic plane `hypRiem`

`hypRiem : RiemData 2` (`Hyp.V = 2 cosh d`, weight `W = V`).  With the generator `L = Δ_g − ∇W·∇` and `Γ(V) = V² − 4`
one has `L V = −V² + 2V + 4` (`hyp_L_V`): quadratic growth of `L` of the distance-like function `V`, which violates the
scale-invariant growth `|Lψ| ≤ C(1+ψ)` of `RadialJets` for both natural exhaustions `V` and `ψ = log(1+V)`
(`hyp_not_radialJets_V`, `hyp_not_radialJets_psi`).  This does NOT prove that `hypRiem.toEll.CoreCut` fails
(AUDIT_R19_CORE2ELL §6: by-hand, polar coordinates); see `STATEMENTS_R22_E4.md`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open Hyp

namespace hypRiem

lemma wg_eq (z : Rd 2) : hypRiem.wg z = E (-1) z := by
  show (Matrix.det (Matrix.of fun i j : Fin 2 => G i j z)) ^ (-(1 / 2 : ℝ)) = _
  exact G_det_rpow z

lemma Γ_V_eq (z : Rd 2) : hypRiem.toEll.Γ V V z = V z ^ 2 - 4 := by
  show ∑ i, ∑ j, hypRiem.g i j z * pderiv V i z * pderiv V j z = _
  simp only [Fin.sum_univ_two, g_eq, pderiv_V, G]
  simp
  have := gamma_V z
  linarith

lemma inner0 : (fun y : Rd 2 => hypRiem.wg y * ∑ j, hypRiem.g 0 j y * pderiv hypRiem.W j y) =
    fun y => 2 * y 0 := by
  funext y
  show hypRiem.wg y * ∑ j, G 0 j y * pderiv V j y = _
  rw [wg_eq]
  simp only [Fin.sum_univ_two, pderiv_V, G]
  simp
  have h : E (-1) y * E 2 y * E (-1) y = 1 := by
    unfold E
    rw [← Real.exp_add, ← Real.exp_add]
    have : -1 * y 1 + 2 * y 1 + -1 * y 1 = 0 := by ring
    rw [this, Real.exp_zero]
  linear_combination (2 * y 0) * h

lemma inner1 : (fun y : Rd 2 => hypRiem.wg y * ∑ j, hypRiem.g 1 j y * pderiv hypRiem.W j y) =
    fun y => 1 - E (-2) y * (1 + y 0 ^ 2) := by
  funext y
  show hypRiem.wg y * ∑ j, G 1 j y * pderiv V j y = _
  rw [wg_eq]
  simp only [Fin.sum_univ_two, pderiv_V, G]
  simp
  have h1 : E (-1) y * E 1 y = 1 := by
    unfold E; rw [← Real.exp_add]; simp
  have h2 : E (-1) y * E (-1) y = E (-2) y := by
    unfold E; rw [← Real.exp_add]; ring_nf
  linear_combination h1 - (1 + y 0 ^ 2) * h2 + 0 * h1

lemma Δg_V (z : Rd 2) : hypRiem.Δg V z = 2 * V z := by
  have e0 : (fun y : Rd 2 => hypRiem.wg y * ∑ j, hypRiem.g 0 j y * pderiv V j y) = fun y => 2 * y 0 :=
    inner0
  have e1 : (fun y : Rd 2 => hypRiem.wg y * ∑ j, hypRiem.g 1 j y * pderiv V j y) =
      fun y => 1 - E (-2) y * (1 + y 0 ^ 2) := inner1
  have d0 : pderiv (fun y : Rd 2 => 2 * y 0) 0 z = 2 := by
    rw [pderiv_mul' contDiff_const (contDiff_apply ℝ ℝ 0), pderiv_const, pderiv_coord]; simp
  have d1 : pderiv (fun y : Rd 2 => 1 - E (-2) y * (1 + y 0 ^ 2)) 1 z =
      2 * E (-2) z * (1 + z 0 ^ 2) := by
    rw [pderiv_sub' contDiff_const ((sm_E (-2)).mul (contDiff_const.add sm_x2)), pderiv_const,
      pderiv_mul' (sm_E (-2)) (contDiff_const.add sm_x2), pderiv_E,
      pderiv_add' contDiff_const sm_x2, pderiv_const, pderiv_x2]
    simp
  unfold RiemData.Δg
  rw [Fin.sum_univ_two, e0, e1, d0, d1, wg_eq]
  have h1 := E_pos 1 z
  have h2 : E (-1) z = (E 1 z)⁻¹ := E_neg 1 z
  have h3 : E (-2) z = (E 1 z ^ 2)⁻¹ := by rw [E_neg, E_two]
  unfold V
  rw [h2, h3]
  field_simp
  ring

/-- **H1**: `L V = −V² + 2V + 4` on the hyperbolic plane (`L = Δ_g − ∇W·∇`, `W = V`, `ΔV = 2V`, `Γ(V) = V² − 4`). -/
theorem hyp_L_V (z : Rd 2) : hypRiem.toEll.L V z = -(V z) ^ 2 + 2 * V z + 4 := by
  rw [hypRiem.riem_L_eq sm_V z, Δg_V]
  have : ∑ i, ∑ j, hypRiem.g i j z * pderiv hypRiem.W i z * pderiv V j z = V z ^ 2 - 4 := by
    rw [← Γ_V_eq]; rfl
  rw [this]; ring

/-- **H1**: `Γ(V) = V² − 4` (`Γ(cosh d) = sinh² d`). -/
theorem hyp_Γ_V (z : Rd 2) : hypRiem.toEll.Γ V V z = V z ^ 2 - 4 := Γ_V_eq z

/-- the point `(x, 0)` of the chart -/
def pt (x : ℝ) : Rd 2 := fun i => if i = 0 then x else 0

lemma V_pt (x : ℝ) : V (pt x) = 2 + x ^ 2 := by
  simp [V, E, pt]
  ring

/-- `L ψ = LV/(1+V) − Γ(V)/(1+V)²` for `ψ = log(1+V)` (through `exp ∘ ψ = 1 + V`, avoiding the singularity of `log`). -/
lemma L_psi (z : Rd 2) : hypRiem.toEll.L psi z =
    hypRiem.toEll.L V z / (1 + V z) - hypRiem.toEll.Γ V V z / (1 + V z) ^ 2 := by
  have e : (fun y : Rd 2 => Real.exp (psi y)) = fun y => 1 + V y := by
    funext y
    simp only [psi]
    exact Real.exp_log (one_add_V_pos y)
  have he : Real.exp (psi z) = 1 + V z := by
    simp only [psi]; exact Real.exp_log (one_add_V_pos z)
  have hS1 : S1 (fun s : ℝ => 1 + s) := contDiff_const.add contDiff_id
  have hd1 : deriv (fun s : ℝ => 1 + s) = fun _ => 1 := by funext s; simp
  have hL1 := hypRiem.toEll.L_comp1 Real.contDiff_exp sm_psi z
  have hΓ1 := hypRiem.toEll.Γ_comp1 Real.contDiff_exp Real.contDiff_exp sm_psi z
  have hL2 := hypRiem.toEll.L_comp1 hS1 sm_V z
  have hΓ2 := hypRiem.toEll.Γ_comp1 hS1 hS1 sm_V z
  rw [e] at hL1 hΓ1
  simp only [Real.deriv_exp, he, hd1, deriv_const, one_mul, zero_mul, add_zero, mul_one] at hL1 hΓ1 hL2 hΓ2
  have hv := one_add_V_pos z
  have hA : hypRiem.toEll.L V z = (1 + V z) * (hypRiem.toEll.L psi z + hypRiem.toEll.Γ psi psi z) := by
    rw [← hL2, hL1]; ring
  have hB : hypRiem.toEll.Γ V V z = (1 + V z) ^ 2 * hypRiem.toEll.Γ psi psi z := by
    rw [← hΓ2, hΓ1]; ring
  rw [hA, hB]
  field_simp
  ring

lemma L_psi_le (z : Rd 2) : hypRiem.toEll.L psi z ≤ -(V z - 5) := by
  have hv : 0 < 1 + V z := one_add_V_pos z
  have h2 := two_le_V z
  rw [L_psi, hyp_L_V, hyp_Γ_V, div_sub_div _ _ hv.ne' (pow_pos hv 2).ne', div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (V z), mul_pos hv hv]

/-- **H3**: no `C` with `|L V| ≤ C (1 + V)`. -/
theorem hyp_L_V_unbounded : ¬ ∃ C : ℝ, ∀ z : Rd 2, |hypRiem.toEll.L V z| ≤ C * (1 + V z) := by
  rintro ⟨C, hC⟩
  set c := |C| with hc
  have hc0 : 0 ≤ c := abs_nonneg C
  have h := hC (pt (c + 6))
  rw [hyp_L_V, V_pt] at h
  have hCc : C ≤ c := le_abs_self C
  have hs : 0 ≤ 1 + (2 + (c + 6) ^ 2) := by positivity
  have h' : |-(2 + (c + 6) ^ 2) ^ 2 + 2 * (2 + (c + 6) ^ 2) + 4| ≤ c * (1 + (2 + (c + 6) ^ 2)) :=
    h.trans (mul_le_mul_of_nonneg_right hCc hs)
  have h'' := (abs_le.1 h').1
  nlinarith [sq_nonneg c, sq_nonneg (c + 6), mul_nonneg hc0 hc0]

/-- **H3**: no `C` with `|L ψ| ≤ C (1 + ψ)`, `ψ = log(1+V)`. -/
theorem hyp_L_psi_unbounded : ¬ ∃ C : ℝ, ∀ z : Rd 2, |hypRiem.toEll.L psi z| ≤ C * (1 + psi z) := by
  rintro ⟨C, hC⟩
  set c := |C| with hc
  have hc0 : 0 ≤ c := abs_nonneg C
  set y0 : ℝ := 2 * c + 6 with hy0
  have hy0pos : 6 ≤ y0 := by linarith
  set x : ℝ := Real.sqrt (y0 ^ 2 - 3) with hx
  have hx2 : x ^ 2 = y0 ^ 2 - 3 := Real.sq_sqrt (by nlinarith)
  have hV : V (pt x) = y0 ^ 2 - 1 := by rw [V_pt, hx2]; ring
  have h := hC (pt x)
  have hle := L_psi_le (pt x)
  rw [hV] at hle
  have hψ : psi (pt x) ≤ 2 * (y0 - 1) := by
    have : psi (pt x) = 2 * Real.log y0 := by
      simp only [psi]
      rw [hV, show 1 + (y0 ^ 2 - 1) = y0 ^ 2 by ring, Real.log_pow]
      norm_num
    rw [this]
    have := Real.log_le_sub_one_of_pos (show 0 < y0 by linarith)
    linarith
  have hCc : C ≤ c := le_abs_self C
  have hpos : 0 ≤ 1 + psi (pt x) := by
    have : 0 ≤ psi (pt x) := by
      simp only [psi]
      exact Real.log_nonneg (by linarith [two_le_V (pt x)])
    linarith
  have h1 : |hypRiem.toEll.L psi (pt x)| ≤ c * (1 + psi (pt x)) :=
    h.trans (mul_le_mul_of_nonneg_right hCc hpos)
  have h2 : c * (1 + psi (pt x)) ≤ c * (1 + 2 * (y0 - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  have h3 : -hypRiem.toEll.L psi (pt x) ≤ |hypRiem.toEll.L psi (pt x)| := neg_le_abs _
  nlinarith [sq_nonneg c]

/-- **H2**: the `RadialJets` hypothesis fails for the exhaustion `V = 2cosh d`. -/
theorem hyp_not_radialJets_V (α β : ℝ → ℝ) : ¬ RadialJets hypRiem.toEll V α β := by
  intro hJ
  obtain ⟨C, _, hC⟩ := hJ.growth
  refine hyp_L_V_unbounded ⟨C, fun z => ?_⟩
  have := (hC (V z) (by linarith [two_le_V z])).1
  rwa [← hJ.L_eq z] at this

/-- **H2**: the `RadialJets` hypothesis fails for the exhaustion `ψ = log(1+V)` of `HypExample`. -/
theorem hyp_not_radialJets_psi (α β : ℝ → ℝ) : ¬ RadialJets hypRiem.toEll psi α β := by
  intro hJ
  obtain ⟨C, _, hC⟩ := hJ.growth
  refine hyp_L_psi_unbounded ⟨C, fun z => ?_⟩
  have := (hC (psi z) (hJ.nonneg z)).1
  rwa [← hJ.L_eq z] at this

end hypRiem

end MarkovTriple.BGL.Instances.Riemannian
