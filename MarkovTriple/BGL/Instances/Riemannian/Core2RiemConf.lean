import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.Core2RiemMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllRadialMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdExample

/-!
# The non-flat conformal plane `confRiem` satisfies `RadialExh`, hence `Core2` (R19, Stream A6; target T5, variable metric)

`confRiem : RiemData 2`: co-metric `g^{ij} = e^{-|x|²} δ`, weight `W = 2 e^{|x|²}`, `Ric = -2 g`-type curvature, `Curv 2`.
Here `L f = e^{-|x|²} Δ f - 4 x·∇f` (computed from `riem_L_eq`), and `ψ = |x|²/2` satisfies
`Lψ = α(ψ)`, `Γ(ψ) = β(ψ)` with `α(s) = 2e^{-2s} - 8s`, `β(s) = 2s e^{-2s}`: the scale-invariant growth conditions hold with `C = 16`.
Consequently `Core2` and the converse of BGL Prop. 3.3.17 hold on the **non-flat variable-metric** example with `ρ = 2 > 0`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd

namespace confRiem

lemma wg_eq (y : Rd 2) : confRiem.wg y = Real.exp (qd y) := by
  show (Matrix.det (Matrix.of fun i j : Fin 2 => confG i j y)) ^ (-(1 / 2 : ℝ)) = _
  exact confG_det_rpow y

lemma g_apply (i j : Fin 2) (y : Rd 2) : confRiem.g i j y = if i = j then Real.exp (-qd y) else 0 := rfl

lemma inner_eq {f : Rd 2 → ℝ} (i : Fin 2) (y : Rd 2) :
    confRiem.wg y * ∑ j, confRiem.g i j y * pderiv f j y = pderiv f i y := by
  rw [wg_eq]
  simp only [g_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← mul_assoc, ← Real.exp_add]; simp

/-- the generator of the conformal plane: `L f = e^{-|x|²} Δf - 4 x·∇f`. -/
theorem L_formula {f : Rd 2 → ℝ} (hf : Sm f) (x : Rd 2) :
    confRiem.toEll.L f x = Real.exp (-qd x) * ∑ i, pderiv (pderiv f i) i x - 4 * ∑ i, x i * pderiv f i x := by
  rw [confRiem.riem_L_eq hf x]
  have h1 : confRiem.Δg f x = Real.exp (-qd x) * ∑ i, pderiv (pderiv f i) i x := by
    unfold RiemData.Δg
    have : ∀ i, (fun y => confRiem.wg y * ∑ j, confRiem.g i j y * pderiv f j y) = pderiv f i :=
      fun i => funext fun y => inner_eq i y
    simp only [this]
    rw [wg_eq, Real.exp_neg]
  have h2 : ∑ i, ∑ j, confRiem.g i j x * pderiv confRiem.W i x * pderiv f j x = 4 * ∑ i, x i * pderiv f i x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [pderiv_W]
    have : Real.exp (-qd x) * (4 * (Real.exp (qd x) * x i)) * pderiv f i x = 4 * (x i * pderiv f i x) := by
      have h : Real.exp (-qd x) * Real.exp (qd x) = 1 := by rw [← Real.exp_add]; simp
      calc Real.exp (-qd x) * (4 * (Real.exp (qd x) * x i)) * pderiv f i x
          = 4 * (Real.exp (-qd x) * Real.exp (qd x)) * (x i * pderiv f i x) := by ring
        _ = _ := by rw [h]; ring
    exact this
  rw [h1, h2]

end confRiem

/-- `ψ = |x|²/2` -/
noncomputable def confψ (x : Rd 2) : ℝ := qd x / 2

lemma sm_confψ : Sm confψ := sm_qd.div_const 2

/-- `α(s) = 2e^{-2s} - 8s` -/
noncomputable def confα (s : ℝ) : ℝ := 2 * Real.exp (-2 * s) - 8 * s

/-- `β(s) = 2 s e^{-2s}` -/
noncomputable def confβ (s : ℝ) : ℝ := 2 * s * Real.exp (-2 * s)

lemma confα_smooth : S1 confα :=
  (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).sub
    (contDiff_const.mul contDiff_id)

lemma confβ_smooth : S1 confβ :=
  (contDiff_const.mul contDiff_id).mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

lemma hasDerivAt_exp2 (s : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-2 * s)) (-2 * Real.exp (-2 * s)) s := by
  have := ((hasDerivAt_id s).const_mul (-2 : ℝ)).exp
  simpa [mul_comm] using this

lemma deriv_confα : deriv confα = fun s => -4 * Real.exp (-2 * s) - 8 := by
  funext s
  have h : HasDerivAt confα (2 * (-2 * Real.exp (-2 * s)) - 8 * 1) s :=
    ((hasDerivAt_exp2 s).const_mul 2).sub ((hasDerivAt_id s).const_mul 8)
  rw [h.deriv]; ring

lemma deriv_deriv_confα : deriv (deriv confα) = fun s => 8 * Real.exp (-2 * s) := by
  rw [deriv_confα]
  funext s
  have h : HasDerivAt (fun s : ℝ => -4 * Real.exp (-2 * s) - 8) (-4 * (-2 * Real.exp (-2 * s))) s :=
    ((hasDerivAt_exp2 s).const_mul (-4)).sub_const 8
  rw [h.deriv]; ring

lemma deriv_confβ : deriv confβ = fun s => 2 * Real.exp (-2 * s) - 4 * s * Real.exp (-2 * s) := by
  funext s
  have h : HasDerivAt confβ (2 * 1 * Real.exp (-2 * s) + 2 * s * (-2 * Real.exp (-2 * s))) s :=
    (((hasDerivAt_id s).const_mul 2).mul (hasDerivAt_exp2 s))
  rw [h.deriv]; ring

lemma deriv_deriv_confβ : deriv (deriv confβ) = fun s => -8 * Real.exp (-2 * s) + 8 * s * Real.exp (-2 * s) := by
  rw [deriv_confβ]
  funext s
  have h : HasDerivAt (fun s : ℝ => 2 * Real.exp (-2 * s) - 4 * s * Real.exp (-2 * s))
      (2 * (-2 * Real.exp (-2 * s)) - (4 * 1 * Real.exp (-2 * s) + 4 * s * (-2 * Real.exp (-2 * s)))) s :=
    ((hasDerivAt_exp2 s).const_mul 2).sub ((((hasDerivAt_id s).const_mul 4)).mul (hasDerivAt_exp2 s))
  rw [h.deriv]; ring

lemma conf_L_ψ (x : Rd 2) : confRiem.toEll.L confψ x = confα (confψ x) := by
  rw [confRiem.L_formula sm_confψ x]
  have e1 : pderiv confψ = fun i y => y i := by
    funext i
    exact pderiv_gauss_fun i
  have e2 : ∀ i, pderiv (pderiv confψ i) i x = 1 := by
    intro i
    rw [show pderiv confψ i = fun y => y i from congrFun e1 i, pderiv_coord]; simp
  simp only [e2, congrFun (congrFun e1 _), confα, confψ]
  have hq : ∑ i : Fin 2, x i * x i = qd x := by
    unfold qd; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hq]
  simp
  ring_nf

lemma conf_Γ_ψ (x : Rd 2) : confRiem.toEll.Γ confψ confψ x = confβ (confψ x) := by
  have e1 : pderiv confψ = fun i y => y i := by
    funext i
    exact pderiv_gauss_fun i
  unfold EllData.Γ
  have : confRiem.toEll.a = confG := rfl
  rw [this]
  simp only [confG, congrFun (congrFun e1 _), ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    confβ, confψ]
  have hq : ∑ i : Fin 2, Real.exp (-qd x) * x i * x i = Real.exp (-qd x) * qd x := by
    unfold qd; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hq]
  have : -2 * (qd x / 2) = -qd x := by ring
  rw [this]; ring

lemma conf_proper (c : ℝ) : Bornology.IsBounded {x : Rd 2 | confψ x ≤ c} := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : Rd 2)]
  refine ⟨max 1 (2 * c), fun x hx => ?_⟩
  have hx' : qd x ≤ 2 * c := by have : qd x / 2 ≤ c := hx; linarith
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_left _ _))]
  intro i
  rw [Real.norm_eq_abs]
  have hi : x i ^ 2 ≤ qd x :=
    Finset.single_le_sum (f := fun k => x k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  by_cases h : |x i| ≤ 1
  · exact h.trans (le_max_left _ _)
  · push Not at h
    have : |x i| ≤ x i ^ 2 := by nlinarith [sq_abs (x i), abs_nonneg (x i)]
    exact (this.trans (hi.trans hx')).trans (le_max_right _ _)

theorem conf_radialJets : RadialJets confRiem.toEll confψ confα confβ where
  smooth := sm_confψ
  nonneg := fun x => by unfold confψ; have := qd_nonneg x; linarith
  proper := conf_proper
  α_smooth := confα_smooth
  β_smooth := confβ_smooth
  L_eq := conf_L_ψ
  Γ_eq := conf_Γ_ψ
  growth := by
    refine ⟨16, by norm_num, fun s hs => ?_⟩
    have he0 : 0 < Real.exp (-2 * s) := Real.exp_pos _
    have he1 : Real.exp (-2 * s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have hsE : s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
    have h1sE : 1 + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
    have hexp2 : Real.exp (-2 * s) * Real.exp s ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]; linarith
    have hsEx : s * Real.exp (-2 * s) ≤ 1 := by
      calc s * Real.exp (-2 * s) ≤ Real.exp s * Real.exp (-2 * s) :=
            mul_le_mul_of_nonneg_right hsE he0.le
        _ ≤ 1 := by rw [mul_comm]; exact hexp2
    have h1sEx : (1 + s) * Real.exp (-2 * s) ≤ 1 := by
      calc (1 + s) * Real.exp (-2 * s) ≤ Real.exp s * Real.exp (-2 * s) :=
            mul_le_mul_of_nonneg_right h1sE he0.le
        _ ≤ 1 := by rw [mul_comm]; exact hexp2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show |confα s| ≤ _
      unfold confα
      rw [abs_le]; constructor <;> nlinarith
    · show 0 ≤ confβ s
      unfold confβ; positivity
    · show confβ s ≤ _
      unfold confβ
      nlinarith [mul_nonneg hs he0.le]
    · rw [deriv_confα]
      show |-4 * Real.exp (-2 * s) - 8| ≤ _
      rw [abs_le]; constructor <;> nlinarith
    · rw [deriv_confβ]
      show |2 * Real.exp (-2 * s) - 4 * s * Real.exp (-2 * s)| ≤ _
      rw [abs_le]; constructor <;> nlinarith
    · rw [deriv_deriv_confα]
      show |8 * Real.exp (-2 * s)| * (1 + s) ≤ _
      rw [abs_of_pos (by positivity)]
      nlinarith
    · rw [deriv_deriv_confβ]
      show |-8 * Real.exp (-2 * s) + 8 * s * Real.exp (-2 * s)| ≤ _
      rw [abs_le]; constructor <;> nlinarith

/-- **the conformal plane has a cut-off family** -/
theorem confRiem_coreCut : confRiem.toEll.CoreCut :=
  confRiem.toEll.coreCut_of_radial ⟨confψ, confα, confβ, conf_radialJets⟩

/-- **`Core2` on the non-flat, variable-metric, `ρ = 2 > 0` example `confRiem`**. -/
theorem confRiem_core2 : confRiem.riemFull_unconditional.Core2 :=
  confRiem.riem_core2 confRiem.curv confRiem_coreCut

/-- **the converse of BGL Prop. 3.3.17 on `confRiem`** (`Curv 2`). -/
theorem confRiem_mem_domain_of_Γ₂ {f : Rd 2 → ℝ} (hf : f ∈ confRiem.riemFull_unconditional.A)
    (hf2 : MemLp f 2 confRiem.toEll.μ)
    (hG : Integrable (MarkovTriple.BGL.FullTriple.G confRiem.riemFull_unconditional f f) confRiem.toEll.μ)
    (hG2 : Integrable (confRiem.riemFull_unconditional.toDiffusionTriple.Γ₂ f f) confRiem.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ confRiem.riemFull_unconditional.toDiffusionTriple.generator.domain,
      ((confRiem.riemFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 confRiem.toEll.μ) :
        Rd 2 → ℝ) =ᵐ[confRiem.toEll.μ] confRiem.riemFull_unconditional.L f :=
  confRiem.riem_mem_domain_of_Γ₂ confRiem.curv confRiem_coreCut hf hf2 hG hG2

end MarkovTriple.BGL.Instances.Riemannian
