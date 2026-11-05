import Mathlib
import MarkovTriple.Stochastic.R32A2.Lyap
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllRadialCalc
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdCut
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdCalc

/-!
# Round 32 (A2), part 3: the Lyapunov function `h(y) = 1/(1+|y|⁴)` for the Gibbs generator

`h = φ ∘ qd` with `φ(s) = 1/(1+s²)`, `qd(y) = Σ yᵢ²`.  Under `|∂ᵢV| ≤ C (1 + Σ|yⱼ|)` one has `L h ≤ λ h`, `|∂ᵢ h| ≤ 6 h`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.Stochastic.R32A2

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

/-- the one-variable profile `φ(s) = 1/(1+s²)` -/
noncomputable def phi (s : ℝ) : ℝ := (1 + s ^ 2)⁻¹

lemma phi_smooth : S1 phi := by
  refine ContDiff.inv (by fun_prop) fun s => by positivity

lemma hasDerivAt_phi (s : ℝ) : HasDerivAt phi (-(2 * s) / (1 + s ^ 2) ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).const_add 1)
  have := h1.inv (by positivity)
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_ |>.congr_deriv rfl
  exact Filter.Eventually.of_forall fun x => rfl

lemma deriv_phi (s : ℝ) : deriv phi s = -(2 * s) / (1 + s ^ 2) ^ 2 := (hasDerivAt_phi s).deriv

lemma deriv_deriv_phi (s : ℝ) : deriv (deriv phi) s = (6 * s ^ 2 - 2) / (1 + s ^ 2) ^ 3 := by
  have e : deriv phi = fun s => -(2 * s) / (1 + s ^ 2) ^ 2 := funext deriv_phi
  rw [e]
  have h1 : HasDerivAt (fun s : ℝ => -(2 * s)) (-2) s := by
    simpa using ((hasDerivAt_id s).const_mul 2).fun_neg
  have h2 : HasDerivAt (fun s : ℝ => (1 + s ^ 2) ^ 2) (2 * (1 + s ^ 2) * (2 * s)) s := by
    have h : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := by
      simpa using ((hasDerivAt_pow 2 s).const_add 1)
    simpa using h.fun_pow 2
  have := h1.fun_div h2 (by positivity)
  rw [this.deriv]
  field_simp
  ring

/-- the Lyapunov function `h = φ ∘ qd`, `h(y) = 1/(1+|y|⁴)` -/
noncomputable def hL (y : Rd d) : ℝ := phi (qd y)

lemma sm_hL : Sm (hL : Rd d → ℝ) := phi_smooth.comp sm_qd

lemma hL_pos (y : Rd d) : 0 < hL y := by
  unfold hL phi; have := qd_nonneg y; positivity

lemma hL_le_one (y : Rd d) : hL y ≤ 1 := by
  unfold hL phi
  have := qd_nonneg y
  exact inv_le_one_of_one_le₀ (by nlinarith)

lemma pderiv_hL (i : Fin d) (y : Rd d) : pderiv hL i y = deriv phi (qd y) * (2 * y i) := by
  rw [show (hL : Rd d → ℝ) = fun y => phi (qd y) from rfl, pderiv_comp1 phi_smooth sm_qd, pderiv_qd]

lemma sq_le_qd (i : Fin d) (y : Rd d) : y i ^ 2 ≤ qd y :=
  Finset.single_le_sum (f := fun j => y j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

lemma abs_pderiv_hL (i : Fin d) (y : Rd d) : |pderiv hL i y| ≤ 6 * hL y := by
  rw [pderiv_hL, deriv_phi]
  have hq := qd_nonneg y
  have hyi : |y i| ≤ (1 + qd y) / 2 := by
    nlinarith [sq_le_qd i y, sq_abs (y i), sq_nonneg (|y i| - 1)]
  have hpos : 0 < (1 + qd y ^ 2) := by positivity
  have e : -(2 * qd y) / (1 + qd y ^ 2) ^ 2 * (2 * y i) = -(4 * qd y * y i) / (1 + qd y ^ 2) ^ 2 := by
    field_simp
    ring
  rw [e, abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + qd y ^ 2) ^ 2), abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * qd y)]
  unfold hL phi
  rw [div_le_iff₀ (by positivity)]
  have : 4 * qd y * |y i| ≤ 6 * (1 + qd y ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hyi (by positivity : (0:ℝ) ≤ 4 * qd y), sq_nonneg (qd y - 1)]
  calc 4 * qd y * |y i| ≤ 6 * (1 + qd y ^ 2) := this
    _ = 6 * (1 + qd y ^ 2)⁻¹ * (1 + qd y ^ 2) ^ 2 := by field_simp

lemma pderiv_pderiv_qd (i : Fin d) (y : Rd d) : pderiv (pderiv qd i) i y = 2 := by
  have e : pderiv qd i = fun x : Rd d => 2 * x i := funext (pderiv_qd i)
  rw [e]
  rw [pderiv_mul' (f := fun _ : Rd d => (2 : ℝ)) contDiff_const (contDiff_apply ℝ ℝ i) i y,
    pderiv_const, pderiv_coord]
  simp

lemma Lr_qd (V : Rd d → ℝ) (y : Rd d) : Lr V qd y = ∑ i, (2 - pderiv V i y * (2 * y i)) := by
  unfold Lr
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_pderiv_qd, pderiv_qd]

lemma Gr_qd (y : Rd d) : Gr qd qd y = 4 * qd y := by
  unfold Gr
  simp only [pderiv_qd]
  unfold qd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma Lr_hL (G : GibbsRdData d) (y : Rd d) :
    Lr G.V hL y = deriv phi (qd y) * Lr G.V qd y + deriv (deriv phi) (qd y) * (4 * qd y) := by
  have h := EllData.L_comp1 G.toEll phi_smooth sm_qd y
  rw [G.toEll_L (f := fun y => phi (qd y)) (phi_smooth.comp sm_qd), G.toEll_L sm_qd, G.toEll_Γ,
    Gr_qd] at h
  exact h

lemma l1_sq_le (y : Rd d) : (∑ j, |y j|) ^ 2 ≤ d * qd y := by
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun j => |y j|)
  simpa [qd, sq_abs] using this

/-- `-L qd ≤ A (1 + qd)` under linear growth of `∇V`. -/
lemma neg_Lr_qd_le (V : Rd d → ℝ) {C : ℝ} (hC : ∀ (x : Rd d) (i : Fin d), |pderiv V i x| ≤ C * (1 + ∑ j, |x j|))
    (y : Rd d) : -Lr V qd y ≤ 3 * max C 0 * (d + 1) * (1 + qd y) := by
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hl0 : 0 ≤ ∑ j, |y j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hV : ∀ i, |pderiv V i y| ≤ C' * (1 + ∑ j, |y j|) := fun i =>
    (hC y i).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  rw [Lr_qd]
  have h1 : -∑ i, (2 - pderiv V i y * (2 * y i)) ≤ ∑ i, (C' * (1 + ∑ j, |y j|)) * (2 * |y i|) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h2 : pderiv V i y * (2 * y i) ≤ |pderiv V i y| * (2 * |y i|) := by
      have : |pderiv V i y * (2 * y i)| = |pderiv V i y| * (2 * |y i|) := by
        rw [abs_mul, abs_mul, abs_two]
      rw [← this]; exact le_abs_self _
    have h3 : |pderiv V i y| * (2 * |y i|) ≤ (C' * (1 + ∑ j, |y j|)) * (2 * |y i|) :=
      mul_le_mul_of_nonneg_right (hV i) (by positivity)
    linarith
  have h4 : ∑ i, (C' * (1 + ∑ j, |y j|)) * (2 * |y i|) = 2 * C' * (1 + ∑ j, |y j|) * ∑ j, |y j| := by
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum]
    ring
  have h5 := l1_sq_le y
  have hq := qd_nonneg y
  set l := ∑ j, |y j| with hl
  have h6 : 2 * C' * (1 + l) * l ≤ 3 * C' * (d + 1) * (1 + qd y) := by
    have h7 : 2 * (1 + l) * l ≤ 3 * (d + 1) * (1 + qd y) := by
      nlinarith [sq_nonneg (l - 1), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    nlinarith
  linarith

/-- **`L h ≤ λ h`** for the Lyapunov function, under linear growth of `∇V` -/
lemma Lr_hL_le (G : GibbsRdData d) {C : ℝ}
    (hC : ∀ (x : Rd d) (i : Fin d), |pderiv G.V i x| ≤ C * (1 + ∑ j, |x j|)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ y, Lr G.V hL y ≤ lam * hL y := by
  set A : ℝ := 3 * max C 0 * (d + 1) with hA
  have hA0 : 0 ≤ A := by
    have := le_max_right C 0
    positivity
  refine ⟨3 * A + 12 + 1, by positivity, fun y => ?_⟩
  rw [Lr_hL]
  have hq := qd_nonneg y
  have hD : 0 < 1 + qd y ^ 2 := by positivity
  have hL1 := neg_Lr_qd_le G.V hC y
  rw [← hA] at hL1
  set L := Lr G.V qd y with hLdef
  rw [deriv_phi, deriv_deriv_phi]
  unfold hL phi
  have t1 : -(2 * qd y) / (1 + qd y ^ 2) ^ 2 * L ≤ 3 * A * (1 + qd y ^ 2)⁻¹ := by
    have h1 : -(2 * qd y) * L ≤ 3 * A * (1 + qd y ^ 2) := by
      have : -(2 * qd y) * L = 2 * qd y * (-L) := by ring
      rw [this]
      calc 2 * qd y * (-L) ≤ 2 * qd y * (A * (1 + qd y)) :=
            mul_le_mul_of_nonneg_left hL1 (by positivity)
        _ ≤ 3 * A * (1 + qd y ^ 2) := by nlinarith [sq_nonneg (qd y - 1), mul_nonneg hA0 (sq_nonneg (qd y - 1))]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc -(2 * qd y) * L ≤ 3 * A * (1 + qd y ^ 2) := h1
      _ = 3 * A * (1 + qd y ^ 2)⁻¹ * (1 + qd y ^ 2) ^ 2 := by field_simp
  have t2 : (6 * qd y ^ 2 - 2) / (1 + qd y ^ 2) ^ 3 * (4 * qd y) ≤ 12 * (1 + qd y ^ 2)⁻¹ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : 12 * (1 + qd y ^ 2)⁻¹ * (1 + qd y ^ 2) ^ 3 = 12 * (1 + qd y ^ 2) ^ 2 := by field_simp
    rw [this]
    nlinarith [sq_nonneg (qd y - 1), mul_nonneg hq (sq_nonneg (qd y - 1)), sq_nonneg (qd y ^ 2 - qd y)]
  have hpos : 0 < (1 + qd y ^ 2)⁻¹ := inv_pos.2 hD
  nlinarith

end MarkovTriple.Stochastic.R32A2
