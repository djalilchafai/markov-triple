import Mathlib
import MarkovTriple.Stochastic.R30.MehlerBasic
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDerivAux3

/-!
# Round 30 (S), part 3: pointwise time derivative of the Mehler average

With `aa s = e^{-s}`, `cc s = √(1 - e^{-2s})`: for `φ ∈ C_c^∞` and `s > 0`,
`d/ds Mh (aa s) (cc s) φ (x) = Lou (Mh (aa s) (cc s) φ) (x)` (differentiation under the integral sign and Gaussian integration by parts).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R30

open MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ : (Fin d → ℝ) → ℝ}

/-- `e^{-s}` -/
noncomputable def aa (s : ℝ) : ℝ := Real.exp (-s)
/-- `√(1 - e^{-2s})` -/
noncomputable def cc (s : ℝ) : ℝ := √(1 - Real.exp (-2 * s))

lemma exp_lt_one' {y : ℝ} (hy : y < 0) : Real.exp y < 1 := by
  have := Real.exp_lt_exp.2 hy
  simpa using this

lemma aa_pos (s : ℝ) : 0 < aa s := Real.exp_pos _

lemma aa_le_one {s : ℝ} (hs : 0 ≤ s) : aa s ≤ 1 := Real.exp_le_one_iff.2 (by linarith)

lemma aa_sq (s : ℝ) : aa s ^ 2 = Real.exp (-2 * s) := by
  rw [aa, ← Real.exp_nat_mul]; congr 1; push_cast; ring

lemma cc_sq {s : ℝ} (hs : 0 ≤ s) : cc s ^ 2 = 1 - aa s ^ 2 := by
  rw [cc, Real.sq_sqrt, aa_sq]
  have : Real.exp (-2 * s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

lemma cc_pos {s : ℝ} (hs : 0 < s) : 0 < cc s := by
  rw [cc]; apply Real.sqrt_pos.2
  have : Real.exp (-2 * s) < 1 := exp_lt_one' (by linarith)
  linarith

lemma cc_mono {s s' : ℝ} (h : s ≤ s') : cc s ≤ cc s' := by
  rw [cc, cc]; apply Real.sqrt_le_sqrt
  have : Real.exp (-2 * s') ≤ Real.exp (-2 * s) := Real.exp_le_exp.2 (by linarith)
  linarith

lemma hasDerivAt_aa (s : ℝ) : HasDerivAt aa (-aa s) s := by
  show HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-s)) s
  simpa using (hasDerivAt_neg s).exp

lemma hasDerivAt_cc {s : ℝ} (hs : 0 < s) : HasDerivAt cc (aa s ^ 2 / cc s) s := by
  have h1 : HasDerivAt (fun σ : ℝ => 1 - Real.exp (-2 * σ)) (2 * Real.exp (-2 * s)) s := by
    have := ((hasDerivAt_id s).const_mul (-2 : ℝ)).exp
    refine (this.const_sub 1).congr_deriv ?_
    simp only [id]; ring
  have hpos : 0 < 1 - Real.exp (-2 * s) := by
    have : Real.exp (-2 * s) < 1 := exp_lt_one' (by linarith)
    linarith
  have h2 := h1.sqrt hpos.ne'
  have hc := cc_pos hs
  have hcdef : cc = fun y => √(1 - Real.exp (-2 * y)) := rfl
  rw [hcdef]
  convert h2 using 1
  rw [aa_sq]
  show Real.exp (-2 * s) / cc s = 2 * Real.exp (-2 * s) / (2 * cc s)
  have := hc.ne'
  field_simp

lemma exists_bound_dd (hφ : φ ∈ A₀ d) : ∃ B : ℝ, 0 ≤ B ∧ ∀ i y, |dd i φ y| ≤ B := by
  choose B hB0 hB using fun i => exists_bound (dd_mem hφ i)
  refine ⟨∑ i, B i, Finset.sum_nonneg fun i _ => hB0 i, fun i y => ?_⟩
  exact (hB i y).trans (Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_univ i))

lemma integrable_abs_gam (i : Fin d) : Integrable (fun z : Fin d → ℝ => |z i|) (gam d) := by
  simpa using integrable_abs_pow_gam 1 i

/-- pointwise time derivative of the Mehler average (the `∂_s Q_s = L Q_s` identity) -/
theorem hasDerivAt_Mh_time (hφ : φ ∈ A₀ d) (x : Fin d → ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => Mh (aa σ) (cc σ) φ x) (Lou (Mh (aa s) (cc s) φ) x) s := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_dd hφ
  set m : ℝ := (cc (s / 2))⁻¹ with hm
  have hc2 : 0 < cc (s / 2) := cc_pos (by linarith)
  have hm0 : 0 ≤ m := by positivity
  -- the derivative integrand
  let F' : ℝ → (Fin d → ℝ) → ℝ := fun σ z =>
    ∑ i, ((-aa σ) * x i + (aa σ ^ 2 / cc σ) * z i) * dd i φ (aa σ • x + cc σ • z)
  have hdiff : ∀ z : Fin d → ℝ, ∀ σ : ℝ, 0 < σ →
      HasDerivAt (fun σ => φ (aa σ • x + cc σ • z)) (F' σ z) σ := by
    intro z σ hσ
    have h1 : HasDerivAt (fun σ => aa σ • x + cc σ • z)
        ((-aa σ) • x + (aa σ ^ 2 / cc σ) • z) σ :=
      ((hasDerivAt_aa σ).smul_const x).add ((hasDerivAt_cc hσ).smul_const z)
    have h2 := (hasFDerivAt_of (smooth hφ) (aa σ • x + cc σ • z)).comp_hasDerivAt σ h1
    refine h2.congr_deriv ?_
    rw [fderiv_eq_sum]
    simp [F']
  have hbd : ∀ σ ∈ Metric.ball s (s / 2), ∀ z : Fin d → ℝ,
      ‖F' σ z‖ ≤ ∑ i, (|x i| + m * |z i|) * B := by
    intro σ hσ z
    have hσ' : s / 2 ≤ σ := by
      have := (Metric.mem_ball.1 hσ); rw [Real.dist_eq, abs_lt] at this; linarith
    have hσpos : 0 < σ := by linarith
    have ha1 := aa_le_one hσpos.le
    have ha0 := aa_pos σ
    have hcσ : cc (s / 2) ≤ cc σ := cc_mono hσ'
    have hk : aa σ ^ 2 / cc σ ≤ m := by
      rw [hm]
      calc aa σ ^ 2 / cc σ ≤ 1 / cc σ := by
            apply div_le_div_of_nonneg_right _ (cc_pos hσpos).le; nlinarith
        _ ≤ 1 / cc (s / 2) := one_div_le_one_div_of_le hc2 hcσ
        _ = _ := by simp
    have hk0 : 0 ≤ aa σ ^ 2 / cc σ := by have := cc_pos hσpos; positivity
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_mul ?_ (hB i _) (abs_nonneg _) (by positivity)
    calc |(-aa σ) * x i + (aa σ ^ 2 / cc σ) * z i|
        ≤ |(-aa σ) * x i| + |(aa σ ^ 2 / cc σ) * z i| := abs_add_le _ _
      _ ≤ |x i| + m * |z i| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha0, abs_of_nonneg hk0]
        have : aa σ * |x i| ≤ |x i| := by nlinarith [abs_nonneg (x i)]
        have : (aa σ ^ 2 / cc σ) * |z i| ≤ m * |z i| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
        linarith
  have hbint : Integrable (fun z : Fin d → ℝ => ∑ i, (|x i| + m * |z i|) * B) (gam d) :=
    integrable_finsetSum _ fun i _ =>
      (((integrable_const _).add ((integrable_abs_gam i).const_mul m)).mul_const B)
  have hF'meas : ∀ σ, AEStronglyMeasurable (F' σ) (gam d) := fun σ => by
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_const.add (continuous_const.mul (continuous_apply i))).mul
      ((smooth (dd_mem hφ i)).continuous.comp (by fun_prop))
  have hFmeas : ∀ σ, AEStronglyMeasurable (fun z => φ (aa σ • x + cc σ • z)) (gam d) := fun σ =>
    ((smooth hφ).continuous.comp (by fun_prop)).aestronglyMeasurable
  obtain ⟨_, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gam d)
    (F := fun σ z => φ (aa σ • x + cc σ • z)) (F' := F') (x₀ := s) (bound := fun z => ∑ i, (|x i| + m * |z i|) * B)
    (Metric.ball_mem_nhds s (by linarith)) (Eventually.of_forall hFmeas) (integrable_comp_Mh hφ _ _ x)
    (hF'meas s) (ae_of_all _ fun z σ hσ => hbd σ hσ z) hbint
    (ae_of_all _ fun z σ hσ => hdiff z σ (by
      have := (Metric.mem_ball.1 hσ); rw [Real.dist_eq, abs_lt] at this; linarith))
  -- identify the value
  have hval : ∫ z, F' s z ∂(gam d) = Lou (Mh (aa s) (cc s) φ) x := by
    set a := aa s with ha
    set c := cc s with hc
    have hcpos : 0 < c := cc_pos hs
    have hint1 : ∀ i, Integrable (fun z => (-a) * x i * dd i φ (a • x + c • z)) (gam d) := fun i =>
      (integrable_comp_Mh (dd_mem hφ i) a c x).const_mul _
    have hint2 : ∀ i, Integrable (fun z => (a ^ 2 / c) * (z i * dd i φ (a • x + c • z))) (gam d) := by
      intro i
      refine Integrable.const_mul ?_ _
      obtain ⟨Bi, -, hBi⟩ := exists_bound (dd_mem hφ i)
      refine Integrable.mono' ((integrable_abs_gam i).mul_const Bi)
        (((continuous_apply i).mul ((smooth (dd_mem hφ i)).continuous.comp (by fun_prop))).aestronglyMeasurable)
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hBi _) (abs_nonneg _)
    have e1 : ∀ z, F' s z = ∑ i, ((-a) * x i * dd i φ (a • x + c • z) +
        (a ^ 2 / c) * (z i * dd i φ (a • x + c • z))) := fun z =>
      Finset.sum_congr rfl fun i _ => by ring
    simp_rw [e1]
    rw [integral_finsetSum (μ := gam d) Finset.univ
      (f := fun i z => (-a) * x i * dd i φ (a • x + c • z) +
        (a ^ 2 / c) * (z i * dd i φ (a • x + c • z))) (fun i _ => (hint1 i).add (hint2 i))]
    have e2 : ∀ i, ∫ z, ((-a) * x i * dd i φ (a • x + c • z) +
        (a ^ 2 / c) * (z i * dd i φ (a • x + c • z))) ∂(gam d) =
        (-a) * (x i * Mh a c (dd i φ) x) + a ^ 2 * Mh a c (dd i (dd i φ)) x := by
      intro i
      rw [integral_add (hint1 i) (hint2 i)]
      have hib := gam_ibp_dd hφ (-c) (a • x) i
      simp only [neg_smul, sub_neg_eq_add, neg_neg] at hib
      rw [integral_const_mul, integral_const_mul, hib, integral_const_mul]
      have hcs : c ≠ 0 := hcpos.ne'
      simp only [Mh]
      field_simp
    simp_rw [e2]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Lou_Mh hφ a c x]
    have : ∑ i, Mh a c (dd i (dd i φ)) x = Mh a c (Lf φ) x := by
      unfold Mh Lf
      exact (integral_finsetSum (μ := gam d) Finset.univ
        (f := fun i z => dd i (dd i φ) (a • x + c • z))
        (fun i _ => integrable_comp_Mh (dd_mem (dd_mem hφ i) i) a c x)).symm
    rw [this]
    ring
  rw [← hval]
  exact hD

end MarkovTriple.Stochastic.R30
