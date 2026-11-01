import MarkovTriple.Sanity.OU.MehlerHermite
import MarkovTriple.Sanity.OU.Stable

/-! # OU (Part 18): the Mehler formula `P_t f = Mh e^{-t} √(1-e^{-2t}) f` (a.e.), `f ∈ C_c^∞`

Proof: both sides lie in `L²(γ)` and have the same Hermite coefficients `e^{-nt}⟨h_n, f⟩`
(rotation invariance of `γ ⊗ γ` + the Hermite identity `E He_n(a z + b W) = aⁿ He_n(z)`). -/

open MeasureTheory Filter Topology Polynomial ProbabilityTheory
open scoped ENNReal NNReal Real InnerProductSpace

namespace MarkovTriple.Sanity.OU

open MarkovTriple.Sanity.Circle (IsSG)

lemma coeff_Mh {a c : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hc : c = √(1 - a ^ 2)) {f : ℝ → ℝ}
    (hf : f ∈ A₀) (n : ℕ) :
    ∫ x, hh n x * Mh a c f x ∂γ = a ^ n * ∫ x, hh n x * f x ∂γ := by
  have hac : a ^ 2 + c ^ 2 = 1 := by rw [hc, Real.sq_sqrt (by nlinarith)]; ring
  obtain ⟨B, hB⟩ := A₀.bdd hf
  set θ := Real.arccos a
  have hcos : Real.cos θ = a := Real.cos_arccos (by linarith) ha1
  have hsin : Real.sin θ = c := by rw [Real.sin_arccos, hc]
  set R : ℝ × ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.rotation θ with hRdef
  have hR : ∀ p : ℝ × ℝ, R p = (a * p.1 + c * p.2, -c * p.1 + a * p.2) := by
    intro p; simp [hRdef, ContinuousLinearMap.rotation_apply, hcos, hsin]
  have hmap : (γ.prod γ).map R = γ.prod γ := IsGaussian.map_rotation_eq_self (by simp [integral_id_gaussianReal]) θ
  set G : ℝ × ℝ → ℝ := fun p => hh n (a * p.1 - c * p.2) * f p.1 with hG
  set F : ℝ × ℝ → ℝ := fun p => hh n p.1 * f (a * p.1 + c * p.2) with hF
  have hGR : ∀ p : ℝ × ℝ, G (R p) = F p := by
    intro p
    simp only [hG, hF, hR]
    have : a * (a * p.1 + c * p.2) - c * (-c * p.1 + a * p.2) = p.1 := by
      linear_combination p.1 * hac
    rw [this]
  have hFm : AEStronglyMeasurable F (γ.prod γ) :=
    (((hh_sm n).continuous.comp continuous_fst).mul
      (hf.1.continuous.comp (by fun_prop))).aestronglyMeasurable
  have hFint : Integrable F (γ.prod γ) := by
    have h1 : Integrable (fun p : ℝ × ℝ => B * |hh n p.1|) (γ.prod γ) :=
      (((hh_PG n).integrable.abs).comp_fst γ).const_mul B
    refine h1.mono' hFm (ae_of_all _ fun p => ?_)
    simp only [hF, norm_mul, Real.norm_eq_abs]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _) |>.trans_eq (by ring) |>.trans_eq rfl
  have hGm : AEStronglyMeasurable G (γ.prod γ) :=
    (((hh_sm n).continuous.comp (by fun_prop)).mul (hf.1.continuous.comp continuous_fst)).aestronglyMeasurable
  have hRm : AEMeasurable R (γ.prod γ) := R.continuous.measurable.aemeasurable
  have hGint : Integrable G (γ.prod γ) := by
    have : Integrable G ((γ.prod γ).map R) := by
      rw [integrable_map_measure (by rwa [hmap]) hRm]
      have : G ∘ R = F := funext hGR
      rw [this]; exact hFint
    rwa [hmap] at this
  have hinner : ∀ z, ∫ w, G (z, w) ∂γ = f z * (a ^ n * hh n z) := by
    intro z
    have h1 : ∀ w, G (z, w) = f z * ((√(n.factorial : ℝ))⁻¹ *
        (He n).eval (a * z + (-c) * w)) := by
      intro w; simp only [hG, hh]; ring_nf
    simp_rw [h1]
    rw [integral_const_mul, integral_const_mul,
      (Q_eq a (-c) (by nlinarith) n).1 z]
    simp only [hh]; ring
  calc ∫ x, hh n x * Mh a c f x ∂γ = ∫ x, ∫ y, hh n x * f (a * x + c * y) ∂γ ∂γ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [Mh]; rw [integral_const_mul]
    _ = ∫ p, F p ∂(γ.prod γ) := (integral_prod F hFint).symm
    _ = ∫ p, G (R p) ∂(γ.prod γ) := by simp_rw [hGR]
    _ = ∫ p, G p ∂(γ.prod γ) := by
        rw [← integral_map hRm (by rwa [hmap]), hmap]
    _ = ∫ z, ∫ w, G (z, w) ∂γ ∂γ := integral_prod G hGint
    _ = ∫ z, a ^ n * (hh n z * f z) ∂γ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        dsimp only
        rw [hinner]; ring
    _ = _ := integral_const_mul _ _

lemma memLp_Mh {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 1) {f : ℝ → ℝ} (hf : f ∈ A₀) :
    MemLp (Mh a c f) 2 γ := by
  obtain ⟨C, hC⟩ := decay_Mh ha c hc hf 0
  exact (pg_bounded (sm_Mh a c hf).continuous ⟨C, fun x => by simpa using hC x⟩).memLp_two

section Stable

variable {P : ℝ≥0 → (Lp ℝ 2 γ →L[ℝ] Lp ℝ 2 γ)}

/-- **Mehler formula** for the Ornstein–Uhlenbeck semigroup on test functions, `t > 0`. -/
theorem mehler_ae (hP : MarkovTriple.IsSemigroupOf ouTriple P) (t : ℝ≥0) {f : ℝ → ℝ}
    (hf : f ∈ A₀) (u : Lp ℝ 2 γ) (hu : (u : ℝ → ℝ) =ᵐ[γ] f) :
    ((P t u : Lp ℝ 2 γ) : ℝ → ℝ) =ᵐ[γ] Mh (Real.exp (-(t : ℝ))) (√(1 - Real.exp (-(t : ℝ)) ^ 2)) f := by
  obtain ⟨h0, hadd, hcont, hself, -, -, -, hgen⟩ := hP
  have hsg : IsSG P := ⟨h0, hadd, hcont⟩
  have hgenA : GenA₀ P := fun g hg u v hu hv => hgen g hg u v hu hv
  have hself' : ∀ (t : ℝ≥0) (u v : Lp ℝ 2 γ), ⟪P t u, v⟫_ℝ = ⟪u, P t v⟫_ℝ := hself
  set a := Real.exp (-(t : ℝ)) with ha
  set c := √(1 - a ^ 2) with hc
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by rw [ha]; exact Real.exp_le_one_iff.2 (by simp)
  have hc1 : |c| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.2 (by nlinarith)
  have hMm := memLp_Mh ha0 c hc1 hf
  have hz : P t u - hMm.toLp (Mh a c f) = 0 := by
    refine eq_zero_of_orth_hL fun n => ?_
    rw [inner_sub_right]
    have e1 : ⟪hL n, P t u⟫_ℝ = a ^ n * ∫ x, hh n x * f x ∂γ := by
      refine (hself' t (hL n) u).symm.trans ?_
      rw [eigen_hL hsg hgenA n t, inner_smul_left, inner_hL]
      have : Real.exp (-(n : ℝ) * t) = a ^ n := by
        rw [ha, ← Real.exp_nat_mul]; ring_nf
      simp only [RCLike.conj_to_real, this]
      congr 1
      exact integral_congr_ae (hu.mono fun x hx => by simp only [hx])
    have e2 : ⟪hL n, hMm.toLp (Mh a c f)⟫_ℝ = a ^ n * ∫ x, hh n x * f x ∂γ := by
      rw [inner_hL, ← coeff_Mh ha0 ha1 hc hf n]
      exact integral_congr_ae (hMm.coeFn_toLp.mono fun x hx => by simp only [hx])
    rw [e1, e2, sub_self]
  have := sub_eq_zero.1 hz
  rw [this]
  exact hMm.coeFn_toLp

end Stable

end MarkovTriple.Sanity.OU
