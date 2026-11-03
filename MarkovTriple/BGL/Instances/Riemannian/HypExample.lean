import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.BochnerConverse
import MarkovTriple.BGL.Instances.Riemannian.BochnerExample

/-!
# The hyperbolic plane as a weighted Riemannian chart (non-flat, non-conformal, unbounded co-metric)

Global chart `ℝ² ∋ (x,t) ↦ (x, e^t)` of the half-plane model: `(dx² + dy²)/y² = e^{-2t} dx² + dt²`.  Co-metric
`g^{11} = e^{2t}` (UNBOUNDED), `g^{22} = 1`, `w_g = det(g^{ij})^{-1/2} = e^{-t}`; `K = -1`.
With `u = cosh t + x² e^{-t}/2 = cosh d((x,t),(0,0))` and the weight `W = 2u`, the coordinate formulas of `Curvature.lean` give
`Ric = -g` (`hypRiem.ricci_eq`), `∇∇W = 2u g` (`hypRiem.hess_W`), hence `Ric + ∇∇W = (2u - 1) g ≥ g` and `Curv 1`
(`hypRiem.curv`) by `riem_curv_of_ricci`; `Curv ρ` fails for `ρ > 1` (`hypRiem_not_curv_gt`) by the converse `riem_ricci_of_curv`.
The completeness field `g_exh` is verified with `ψ = log(1 + V)` with `V = 2u` (`Γψ = (V²-4)/(1+V)² ≤ 1`; ERRATA R17-4); the old bounded co-metric hypothesis
would FAIL here (`g^{11} = e^{2t}`).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

namespace Hyp

noncomputable def E (a : ℝ) (z : Rd 2) : ℝ := Real.exp (a * z 1)

lemma E_neg (a : ℝ) (z : Rd 2) : E (-a) z = (E a z)⁻¹ := by
  unfold E; rw [← Real.exp_neg]; ring_nf

lemma E_two (z : Rd 2) : E 2 z = (E 1 z) ^ 2 := by
  unfold E; rw [sq, ← Real.exp_add]; ring_nf

lemma E_pos (a : ℝ) (z : Rd 2) : 0 < E a z := Real.exp_pos _

lemma sm_expl (a : ℝ) : Sm (fun y : Rd 2 => Real.exp (a * y 1)) :=
  (contDiff_const.mul (contDiff_apply ℝ ℝ 1)).exp

lemma sm_E (a : ℝ) : Sm (E a) := sm_expl a

lemma pderiv_expl (a : ℝ) (m : Fin 2) (z : Rd 2) :
    pderiv (fun y : Rd 2 => Real.exp (a * y 1)) m z = if m = 1 then a * Real.exp (a * z 1) else 0 := by
  have h : HasFDerivAt (fun y : Rd 2 => Real.exp (a * y 1))
      (Real.exp (a * z 1) • (a • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)) z :=
    ((hasFDerivAt_apply (1 : Fin 2) z).const_mul a).exp
  unfold pderiv
  rw [h.fderiv]
  fin_cases m <;> simp [mul_comm]

/-- `x²` in the chart -/
lemma sm_x2 : Sm (fun y : Rd 2 => y 0 ^ 2) := (contDiff_apply ℝ ℝ 0).pow 2

lemma pderiv_x2 (m : Fin 2) (z : Rd 2) :
    pderiv (fun y : Rd 2 => y 0 ^ 2) m z = if m = 0 then 2 * z 0 else 0 := by
  have h : HasFDerivAt (fun y : Rd 2 => y 0 ^ 2) ((2 * z 0) • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 2 => ℝ) 0) z := by
    have hd : HasFDerivAt (fun y : Rd 2 => y 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z := hasFDerivAt_apply 0 z
    have := hd.pow 2
    simpa using this
  unfold pderiv
  rw [h.fderiv]
  fin_cases m <;> simp

lemma pderiv_E (a : ℝ) (m : Fin 2) (z : Rd 2) :
    pderiv (E a) m z = if m = 1 then a * E a z else 0 := pderiv_expl a m z

/-- the co-metric `g^{ij} = diag(e^{2t}, 1)` -/
noncomputable def G (i j : Fin 2) (z : Rd 2) : ℝ :=
  if i = j then (if i = 0 then E 2 z else 1) else 0

/-- `V = 2u = e^t + e^{-t} + x² e^{-t}`, where `u = cosh t + x² e^{-t}/2 = cosh d((x,t),(0,0))`; the weight is `W = V` -/
noncomputable def V (z : Rd 2) : ℝ := E 1 z + E (-1) z + z 0 ^ 2 * E (-1) z

lemma sm_V : Sm V := by
  unfold V
  exact ((sm_E 1).add (sm_E (-1))).add (sm_x2.mul (sm_E (-1)))

lemma G_diag (z : Rd 2) :
    (Matrix.of fun i j : Fin 2 => G i j z) = Matrix.diagonal (fun i => if i = 0 then E 2 z else 1) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [G]
  · simp [G, h]

lemma G_det (z : Rd 2) : Matrix.det (Matrix.of fun i j : Fin 2 => G i j z) = E 2 z := by
  rw [G_diag, Matrix.det_diagonal]
  simp

lemma G_det_rpow (z : Rd 2) :
    (Matrix.det (Matrix.of fun i j : Fin 2 => G i j z)) ^ (-(1 / 2 : ℝ)) = E (-1) z := by
  rw [G_det]
  unfold E
  rw [← Real.exp_mul]
  congr 1
  ring

/-- `V = 2u ≥ 2` -/
lemma two_le_V (z : Rd 2) : 2 ≤ V z := by
  unfold V
  have h1 : E 1 z * E (-1) z = 1 := by
    rw [E_neg]; exact mul_inv_cancel₀ (E_pos 1 z).ne'
  have h2 : 2 ≤ E 1 z + E (-1) z := by
    nlinarith [sq_nonneg (E 1 z - E (-1) z), E_pos 1 z, E_pos (-1) z]
  have h3 : 0 ≤ z 0 ^ 2 * E (-1) z := by have := E_pos (-1) z; positivity
  linarith

/-! ### Integrability of the weight `e^{-W} w_g = e^{-V - t}` -/

/-- `e^t + e^{-t} ≥ 1 + |t| + t²/2` -/
lemma cosh_bound (t : ℝ) : 1 + |t| + t ^ 2 / 2 ≤ Real.exp t + Real.exp (-t) := by
  rcases le_total 0 t with h | h
  · have := Real.quadratic_le_exp_of_nonneg h
    have := Real.exp_pos (-t)
    rw [abs_of_nonneg h]; linarith
  · have := Real.quadratic_le_exp_of_nonneg (neg_nonneg.2 h)
    have := Real.exp_pos t
    rw [abs_of_nonpos h]; nlinarith

/-- the density `e^{-V(x,t)} e^{-t}` on `ℝ × ℝ` -/
noncomputable def gW (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(Real.exp p.2 + Real.exp (-p.2) * (1 + p.1 ^ 2))) * Real.exp (-p.2)

lemma gW_eq (x t : ℝ) : gW (x, t) =
    Real.exp (-(Real.exp t + Real.exp (-t))) * Real.exp (-t) * Real.exp (-Real.exp (-t) * x ^ 2) := by
  simp only [gW, ← Real.exp_add]
  congr 1
  ring

lemma continuous_gW : Continuous gW := by
  unfold gW
  fun_prop

lemma integrable_gW : Integrable gW (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod]
  refine (integrable_prod_iff' continuous_gW.aestronglyMeasurable).2 ⟨ae_of_all _ fun t => ?_, ?_⟩
  · have := (integrable_exp_neg_mul_sq (Real.exp_pos (-t))).const_mul
      (Real.exp (-(Real.exp t + Real.exp (-t))) * Real.exp (-t))
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [gW_eq]
  · have hn : ∀ t : ℝ, ∫ x : ℝ, ‖gW (x, t)‖ = Real.exp (-(Real.exp t + Real.exp (-t))) * Real.exp (-t) *
        (Real.sqrt Real.pi * Real.exp (t / 2)) := by
      intro t
      have : ∀ x : ℝ, ‖gW (x, t)‖ = Real.exp (-(Real.exp t + Real.exp (-t))) * Real.exp (-t) *
          Real.exp (-Real.exp (-t) * x ^ 2) := fun x => by
        rw [gW_eq, Real.norm_eq_abs, abs_of_pos (by positivity)]
      simp only [this]
      rw [integral_const_mul, integral_gaussian]
      congr 1
      rw [Real.sqrt_div Real.pi_pos.le, Real.exp_half, Real.exp_neg, Real.sqrt_inv, div_inv_eq_mul]
    simp only [hn]
    have hc : Continuous (fun t : ℝ => Real.exp (-(Real.exp t + Real.exp (-t))) * Real.exp (-t) *
        (Real.sqrt Real.pi * Real.exp (t / 2))) := by fun_prop
    refine Integrable.mono' ((integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul
      (Real.sqrt Real.pi)) hc.aestronglyMeasurable (ae_of_all _ fun t => ?_)
    have hpos : 0 < Real.exp (-(Real.exp t + Real.exp (-t))) * Real.exp (-t) *
        (Real.sqrt Real.pi * Real.exp (t / 2)) := by positivity
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    have e : Real.exp (-(Real.exp t + Real.exp (-t))) * Real.exp (-t) *
        (Real.sqrt Real.pi * Real.exp (t / 2)) =
        Real.sqrt Real.pi * Real.exp (-(Real.exp t + Real.exp (-t)) + -t + t / 2) := by
      rw [Real.exp_add, Real.exp_add]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
    have h1 := cosh_bound t
    have h2 := le_abs_self t
    have h3 := neg_abs_le t
    have h4 := abs_nonneg t
    linarith


lemma integrable_weight : Integrable (fun z : Rd 2 => Real.exp (-(V z)) * E (-1) z) volume := by
  have h := ((volume_preserving_finTwoArrow ℝ).integrable_comp_emb
    (MeasurableEquiv.finTwoArrow.measurableEmbedding)).2 integrable_gW
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [Function.comp, gW, MeasurableEquiv.finTwoArrow_apply, V, E]
  ring_nf
lemma pderiv_V (m : Fin 2) (z : Rd 2) : pderiv V m z =
    if m = 0 then 2 * z 0 * E (-1) z else E 1 z - E (-1) z - z 0 ^ 2 * E (-1) z := by
  unfold V
  rw [pderiv_add' ((sm_E 1).add (sm_E (-1))) (sm_x2.mul (sm_E (-1))),
    pderiv_add' (sm_E 1) (sm_E (-1)), pderiv_mul' sm_x2 (sm_E (-1)), pderiv_x2, pderiv_E, pderiv_E]
  fin_cases m <;> (simp; try ring)

lemma pderiv_V_fun (m : Fin 2) : pderiv V m =
    fun y => if m = 0 then 2 * y 0 * E (-1) y else E 1 y - E (-1) y - y 0 ^ 2 * E (-1) y :=
  funext fun y => pderiv_V m y


/-- the exhaustion function `ψ = log(1 + V)` -/
noncomputable def psi (z : Rd 2) : ℝ := Real.log (1 + V z)

lemma one_add_V_pos (z : Rd 2) : 0 < 1 + V z := by linarith [two_le_V z]

lemma sm_psi : Sm psi := (contDiff_const.add sm_V).log fun z => (one_add_V_pos z).ne'

lemma pderiv_psi (m : Fin 2) (z : Rd 2) : pderiv psi m z = pderiv V m z / (1 + V z) := by
  have h := ((sm_V.hasFDerivAt' z).const_add 1).log (one_add_V_pos z).ne'
  unfold pderiv psi
  rw [h.fderiv]
  simp [div_eq_inv_mul]

/-- `e^{2t} V_x² + V_t² = V² - 4` (`Γ(cosh d) = sinh² d`) -/
lemma gamma_V (z : Rd 2) :
    E 2 z * (2 * z 0 * E (-1) z) ^ 2 + (E 1 z - E (-1) z - z 0 ^ 2 * E (-1) z) ^ 2 = V z ^ 2 - 4 := by
  have h := E_pos 1 z
  unfold V
  rw [E_two, E_neg 1 z]
  field_simp
  ring

lemma exh : ∃ ψ : Rd 2 → ℝ, Sm ψ ∧ (∀ x, 0 ≤ ψ x) ∧ (∀ c : ℝ, Bornology.IsBounded {x : Rd 2 | ψ x ≤ c}) ∧
    ∀ x, ∑ i, ∑ j, G i j x * pderiv ψ i x * pderiv ψ j x ≤ 1 := by
  refine ⟨psi, sm_psi, fun z => Real.log_nonneg (by linarith [two_le_V z]), fun c => ?_, fun z => ?_⟩
  · refine (Metric.isBounded_closedBall (x := (0 : Rd 2)) (r := Real.exp c)).subset ?_
    intro z hz
    have hz' : Real.log (1 + V z) ≤ c := hz
    have hV : V z ≤ Real.exp c := by
      have := (Real.log_le_iff_le_exp (one_add_V_pos z)).1 hz'
      linarith
    have h1 : E 1 z ≤ V z := by
      unfold V; have := E_pos (-1) z; nlinarith [sq_nonneg (z 0), mul_nonneg (sq_nonneg (z 0)) this.le]
    have h2 : E (-1) z ≤ V z := by
      unfold V; have := E_pos 1 z; nlinarith [sq_nonneg (z 0), mul_nonneg (sq_nonneg (z 0)) (E_pos (-1) z).le]
    have h3 : z 0 ^ 2 * E (-1) z ≤ V z := by
      unfold V; have := E_pos 1 z; have := E_pos (-1) z; linarith
    have hK : 0 ≤ Real.exp c := (Real.exp_pos c).le
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hK]
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · -- `x² ≤ V e^t ≤ V²`
      show |z 0| ≤ Real.exp c
      have e1 : E 1 z * E (-1) z = 1 := by rw [E_neg]; exact mul_inv_cancel₀ (E_pos 1 z).ne'
      have h4 : z 0 ^ 2 ≤ V z * V z := by
        have : z 0 ^ 2 = (z 0 ^ 2 * E (-1) z) * E 1 z := by
          calc z 0 ^ 2 = z 0 ^ 2 * (E (-1) z * E 1 z) := by rw [mul_comm (E (-1) z), e1]; ring
            _ = _ := by ring
        rw [this]
        exact mul_le_mul h3 h1 (E_pos 1 z).le (by linarith [two_le_V z])
      have h5 : |z 0| ≤ V z := abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith) (by linarith [two_le_V z]))
      linarith
    · show |z 1| ≤ Real.exp c
      have a1 := Real.add_one_le_exp (z 1)
      have a2 := Real.add_one_le_exp (-z 1)
      have e1 : E 1 z = Real.exp (z 1) := by simp [E]
      have e2 : E (-1) z = Real.exp (-z 1) := by simp [E]
      rw [abs_le]
      constructor <;> linarith
  · have hψ : ∀ m, pderiv psi m z = pderiv V m z / (1 + V z) := fun m => pderiv_psi m z
    simp only [Fin.sum_univ_two, hψ, G, pderiv_V]
    simp
    have key := gamma_V z
    have hpos := one_add_V_pos z
    have e : E 2 z * (2 * z 0 * E (-1) z / (1 + V z)) * (2 * z 0 * E (-1) z / (1 + V z)) +
        (E 1 z - E (-1) z - z 0 ^ 2 * E (-1) z) / (1 + V z) *
        ((E 1 z - E (-1) z - z 0 ^ 2 * E (-1) z) / (1 + V z)) = (V z ^ 2 - 4) / (1 + V z) ^ 2 := by
      rw [← key]; field_simp
    rw [e, div_le_one (by positivity)]
    nlinarith [two_le_V z]

end Hyp

namespace Hyp

end Hyp

open Hyp in
/-- **The hyperbolic plane** `H²` in the global chart `(x,t) ↦ (x, e^t)` with weight `W = V = 2 cosh d(·, o)`. -/
noncomputable def hypRiem : RiemData 2 where
  g := G
  W := V
  g_smooth := fun i j => by
    unfold G
    by_cases h : i = j
    · simp only [h, ite_true]
      by_cases h0 : j = 0
      · simp only [h0, ite_true]; exact sm_E 2
      · simp only [h0, ite_false]; exact contDiff_const
    · simp only [h, ite_false]; exact contDiff_const
  g_symm := fun i j x => by
    unfold G
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  g_posDef := fun x => by
    rw [G_diag, Matrix.posDef_diagonal_iff]
    intro i
    by_cases h : i = 0
    · simp [h, E_pos]
    · simp [h]
  g_exh := exh
  W_smooth := sm_V
  integrable := by
    show Integrable (fun x : Rd 2 => Real.exp (-(V x)) *
      (Matrix.det (Matrix.of fun i j : Fin 2 => G i j x)) ^ (-(1 / 2 : ℝ))) volume
    simp only [G_det_rpow]
    exact integrable_weight

namespace hypRiem
open Hyp

lemma gl_eq (i j : Fin 2) (z : Rd 2) :
    hypRiem.gl i j z = if i = j then (if i = 0 then E (-2) z else 1) else 0 := by
  have hm : hypRiem.mat z = Matrix.diagonal (fun i => if i = 0 then E 2 z else 1) := G_diag z
  have hinv : hypRiem.mat z * Matrix.diagonal (fun i : Fin 2 => if i = 0 then E (-2) z else 1) = 1 := by
    rw [hm, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      by_cases h0 : i = 0
      · simp [h0, E_neg]
        exact mul_inv_cancel₀ (E_pos 2 z).ne'
      · simp [h0]
    · simp [h]
  unfold RiemData.gl
  rw [Matrix.inv_eq_right_inv hinv, Matrix.diagonal_apply]

lemma gl_fun (i j : Fin 2) :
    hypRiem.gl i j = fun y => if i = j then (if i = 0 then E (-2) y else 1) else 0 :=
  funext fun y => gl_eq i j y

lemma pderiv_gl (a b c : Fin 2) (z : Rd 2) :
    pderiv (hypRiem.gl a b) c z = if a = 0 ∧ b = 0 ∧ c = 1 then -2 * E (-2) z else 0 := by
  rw [gl_fun]
  by_cases h : a = b
  · subst h
    by_cases h0 : a = 0
    · simp only [h0, ite_true]
      rw [pderiv_E]
      simp
    · simp only [h0, ite_true, ite_false]
      rw [pderiv_const]
      simp
  · simp only [h, ite_false]
    rw [pderiv_const]
    exact (ite_eq_right_iff.2 fun hc => absurd (hc.1.trans hc.2.1.symm) h).symm

lemma g_eq (a b : Fin 2) (z : Rd 2) : hypRiem.g a b z = G a b z := rfl

lemma E2_mul (z : Rd 2) : E 2 z * E (-2) z = 1 := by
  rw [E_neg]; exact mul_inv_cancel₀ (E_pos 2 z).ne'

/-- Christoffel symbols of the hyperbolic plane: `γ_{00}^1 = e^{-2t}`, `γ_{01}^0 = γ_{10}^0 = -1`, others `0` -/
lemma chr_eq (k i j : Fin 2) (z : Rd 2) : hypRiem.chr k i j z =
    if k = 1 ∧ i = 0 ∧ j = 0 then E (-2) z else if k = 0 ∧ i ≠ j then -1 else 0 := by
  unfold RiemData.chr RiemData.chr1
  simp only [pderiv_gl, g_eq, Fin.sum_univ_two]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [G] <;> linarith [E2_mul z]

lemma pderiv_chr (k i j m : Fin 2) (z : Rd 2) : pderiv (hypRiem.chr k i j) m z =
    if k = 1 ∧ i = 0 ∧ j = 0 then (if m = 1 then -2 * E (-2) z else 0) else 0 := by
  by_cases hc : k = 1 ∧ i = 0 ∧ j = 0
  · have : hypRiem.chr k i j = E (-2) := funext fun y => by rw [chr_eq]; simp [hc]
    rw [this, pderiv_E]; simp [hc]
  · have : hypRiem.chr k i j = fun _ => (if k = 0 ∧ i ≠ j then (-1 : ℝ) else 0) :=
      funext fun y => by rw [chr_eq]; simp [hc]
    rw [this, pderiv_const]; simp [hc]

/-- **Ricci tensor of the hyperbolic plane**: `Ric = -g` -/
theorem ricci_eq (i j : Fin 2) (z : Rd 2) : hypRiem.ricci i j z = -hypRiem.gl i j z := by
  unfold RiemData.ricci RiemData.riem
  simp only [pderiv_chr, chr_eq, gl_eq, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> (simp; try ring)

lemma sm_x : Sm (fun y : Rd 2 => 2 * y 0) := contDiff_const.mul (contDiff_apply ℝ ℝ 0)

lemma pderiv_V0 (i : Fin 2) (z : Rd 2) : pderiv (fun y : Rd 2 => 2 * y 0 * E (-1) y) i z =
    if i = 0 then 2 * E (-1) z else -2 * z 0 * E (-1) z := by
  rw [pderiv_mul' sm_x (sm_E (-1)), pderiv_mul' contDiff_const (contDiff_apply ℝ ℝ 0), pderiv_const,
    pderiv_coord, pderiv_E]
  fin_cases i <;> simp

lemma pderiv_V1 (i : Fin 2) (z : Rd 2) :
    pderiv (fun y : Rd 2 => E 1 y - E (-1) y - y 0 ^ 2 * E (-1) y) i z =
    if i = 0 then -2 * z 0 * E (-1) z else E 1 z + E (-1) z + z 0 ^ 2 * E (-1) z := by
  rw [pderiv_sub' ((sm_E 1).sub (sm_E (-1))) (sm_x2.mul (sm_E (-1))),
    pderiv_sub' (sm_E 1) (sm_E (-1)), pderiv_mul' sm_x2 (sm_E (-1)), pderiv_x2, pderiv_E, pderiv_E]
  fin_cases i <;> simp

/-- **`∇∇W = V g = 2u g`** for the hyperbolic plane (`Hess cosh d = cosh d · g`). -/
theorem hess_W (i j : Fin 2) (z : Rd 2) :
    hypRiem.hess hypRiem.W i j z = V z * hypRiem.gl i j z := by
  show hypRiem.hess V i j z = _
  unfold RiemData.hess
  rw [pderiv_V_fun j]
  simp only [pderiv_V, chr_eq, gl_eq, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [pderiv_V0, pderiv_V1, V]
  have h := E_pos 1 z
  rw [E_neg 2 z, E_two z, E_neg 1 z]
  field_simp
  ring

theorem beRicci_eq (i j : Fin 2) (z : Rd 2) : hypRiem.beRicci i j z = (V z - 1) * hypRiem.gl i j z := by
  unfold RiemData.beRicci
  rw [ricci_eq, hess_W]; ring

lemma gl_quad (z ξ : Rd 2) : ∑ i, ∑ j, hypRiem.gl i j z * ξ i * ξ j = E (-2) z * ξ 0 ^ 2 + ξ 1 ^ 2 := by
  simp only [gl_eq, Fin.sum_univ_two]
  simp
  ring

lemma gl_quad_nonneg (z ξ : Rd 2) : 0 ≤ ∑ i, ∑ j, hypRiem.gl i j z * ξ i * ξ j := by
  rw [gl_quad]; have := E_pos (-2) z; positivity

/-- **Sharp curvature of the hyperbolic plane with weight `W = 2 cosh d`**: `Curv ρ ↔ ρ ≤ 1`, i.e. `Ric + ∇∇W = (V-1) g`
has infimum exactly `g` (attained at the origin `V = 2`): (1.16.8) in both directions. -/
theorem curv_iff {ρ : ℝ} : hypRiem.Curv ρ ↔ ρ ≤ 1 := by
  rw [hypRiem.riem_curv_iff_ricci]
  constructor
  · intro h
    have h1 := h 0 (fun i => if i = 1 then 1 else 0)
    simp only [beRicci_eq] at h1
    have h2 : V 0 = 2 := by simp [V, E]; norm_num
    simp [gl_eq, h2] at h1
    linarith
  · intro hρ z ξ
    have e : ∑ i, ∑ j, hypRiem.beRicci i j z * ξ i * ξ j = (V z - 1) * ∑ i, ∑ j, hypRiem.gl i j z * ξ i * ξ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [beRicci_eq]; ring
    rw [e]
    nlinarith [gl_quad_nonneg z ξ, two_le_V z]

theorem curv : hypRiem.Curv 1 := curv_iff.2 le_rfl

end hypRiem

end MarkovTriple.BGL.Instances.Riemannian
