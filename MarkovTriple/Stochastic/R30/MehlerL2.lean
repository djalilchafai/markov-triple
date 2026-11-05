import Mathlib
import MarkovTriple.Stochastic.R30.MehlerTime
import MarkovTriple.Stochastic.R30.L2Deriv

/-!
# Round 30 (S), part 5: the Mehler flow as an `L²(γ)`-valued map

For `φ ∈ C_c^∞(ℝ^d)` let `Gm φ σ = Mh (e^{-σ}) (√(1-e^{-2σ})) φ` (the Mehler average at time `σ`).  Proved:

* `Gm φ σ` is bounded, `Lou (Gm φ σ)` has linear growth, both are in `L²(γ)`;
* `σ ↦ [Gm φ σ] ∈ L²(γ)` is continuous on `ℝ` (value `[φ]` at `0`) and has the strong derivative `[Lou (Gm φ s)]` at every `s > 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R30

open MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ : (Fin d → ℝ) → ℝ}

/-- the Mehler average at time `σ` -/
noncomputable def Gm (φ : (Fin d → ℝ) → ℝ) (σ : ℝ) : (Fin d → ℝ) → ℝ := Mh (aa σ) (cc σ) φ

lemma Gm_zero (φ : (Fin d → ℝ) → ℝ) : Gm φ 0 = φ := by
  funext x
  have h1 : aa 0 = 1 := by simp [aa]
  have h2 : cc 0 = 0 := by simp [cc]
  simp [Gm, Mh, h1, h2]

lemma continuous_cc : Continuous cc := by
  unfold cc
  exact Real.continuous_sqrt.comp (by fun_prop)

lemma continuous_aa : Continuous aa := by
  unfold aa; fun_prop

lemma continuous_Lou {g : (Fin d → ℝ) → ℝ} (hg : Sm g) : Continuous (Lou g) := by
  unfold Lou
  refine (continuous_finsetSum _ fun i _ => ((hg.dd i).dd i).continuous).sub
    (continuous_finsetSum _ fun i _ => (continuous_apply i).mul (hg.dd i).continuous)

lemma integrable_one_add_norm_sq : Integrable (fun x : Fin d → ℝ => (1 + ‖x‖) ^ 2) (gam d) := by
  have h2 := integrable_norm_pow_gam (d := d) 2
  refine Integrable.mono' ((integrable_const (2 : ℝ)).add (h2.const_mul 2))
    ((continuous_const.add continuous_norm).pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

lemma integrable_sq_mul_one_add_norm (K : ℝ) :
    Integrable (fun x : Fin d → ℝ => (K * (1 + ‖x‖)) ^ 2) (gam d) := by
  have := (integrable_one_add_norm_sq (d := d)).const_mul (K ^ 2)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only [mul_pow]

lemma memLp_of_abs_le {f bnd : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f (gam d))
    (hb : ∀ x, |f x| ≤ bnd x) (hbnd : Integrable (fun x => bnd x ^ 2) (gam d)) : MemLp f 2 (gam d) := by
  rw [memLp_two_iff_integrable_sq hf]
  refine Integrable.mono' hbnd (hf.pow 2) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2

/-- the linear-growth bound of the generator of the Mehler average -/
lemma abs_Lou_Mh_le (hφ : φ ∈ A₀ d) :
    ∃ C₁ B : ℝ, 0 ≤ C₁ ∧ 0 ≤ B ∧ ∀ (a c : ℝ) (x : Fin d → ℝ),
      |Lou (Mh a c φ) x| ≤ (a ^ 2 * C₁ + |a| * (d * B)) * (1 + ‖x‖) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound (Lf_mem hφ)
  obtain ⟨B, hB0, hB⟩ := exists_bound_dd hφ
  refine ⟨C₁, B, hC₁0, hB0, fun a c x => ?_⟩
  rw [Lou_Mh hφ a c x]
  have h1 : |a ^ 2 * Mh a c (Lf φ) x| ≤ a ^ 2 * C₁ := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
    exact mul_le_mul_of_nonneg_left (abs_Mh_le hC₁ a c x) (sq_nonneg a)
  have h2 : |a * ∑ i, x i * Mh a c (dd i φ) x| ≤ |a| * (d * B) * ‖x‖ := by
    rw [abs_mul]
    have : |∑ i, x i * Mh a c (dd i φ) x| ≤ d * B * ‖x‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |x i * Mh a c (dd i φ) x| ≤ ∑ _i : Fin d, ‖x‖ * B := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            exact mul_le_mul (by simpa using norm_le_pi_norm x i) (abs_Mh_le (hB i) a c x)
              (abs_nonneg _) (norm_nonneg _)
        _ = d * B * ‖x‖ := by simp; ring
    calc |a| * |∑ i, x i * Mh a c (dd i φ) x| ≤ |a| * (d * B * ‖x‖) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |a| * (d * B) * ‖x‖ := by ring
  have hn := norm_nonneg x
  calc |a ^ 2 * Mh a c (Lf φ) x - a * ∑ i, x i * Mh a c (dd i φ) x|
      ≤ |a ^ 2 * Mh a c (Lf φ) x| + |a * ∑ i, x i * Mh a c (dd i φ) x| := abs_sub _ _
    _ ≤ a ^ 2 * C₁ + |a| * (d * B) * ‖x‖ := by linarith
    _ ≤ (a ^ 2 * C₁ + |a| * (d * B)) * (1 + ‖x‖) := by
        have : 0 ≤ a ^ 2 * C₁ := by positivity
        have : 0 ≤ |a| * (d * B) := by positivity
        nlinarith

lemma abs_Lou_Gm_le (hφ : φ ∈ A₀ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (σ : ℝ), 0 ≤ σ → ∀ x, |Lou (Gm φ σ) x| ≤ K * (1 + ‖x‖) := by
  obtain ⟨C₁, B, hC₁, hB, h⟩ := abs_Lou_Mh_le hφ
  refine ⟨C₁ + d * B, by positivity, fun σ hσ x => ?_⟩
  refine (h (aa σ) (cc σ) x).trans ?_
  have ha1 := aa_le_one hσ
  have ha0 := aa_pos σ
  have : aa σ ^ 2 * C₁ + |aa σ| * (d * B) ≤ C₁ + d * B := by
    rw [abs_of_pos ha0]
    have h1 : aa σ ^ 2 ≤ 1 := by nlinarith
    have h2 : 0 ≤ (d : ℝ) * B := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

lemma memLp_Gm (hφ : φ ∈ A₀ d) (σ : ℝ) : MemLp (Gm φ σ) 2 (gam d) := by
  obtain ⟨C, hC⟩ := bdd_of_A₀ hφ
  exact MemLp.of_bound ((Mh_smooth hφ (aa σ) (cc σ)).continuous.aestronglyMeasurable) C
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_Mh_le hC _ _ x)

lemma memLp_Lou_Gm (hφ : φ ∈ A₀ d) (σ : ℝ) : MemLp (Lou (Gm φ σ)) 2 (gam d) := by
  obtain ⟨C₁, B, hC₁, hB, h⟩ := abs_Lou_Mh_le hφ
  exact memLp_of_abs_le (continuous_Lou (Mh_smooth hφ (aa σ) (cc σ))).aestronglyMeasurable
    (fun x => h (aa σ) (cc σ) x) (integrable_sq_mul_one_add_norm _)

/-- the Mehler flow as an `L²(γ)`-valued map -/
noncomputable def Qcls (hφ : φ ∈ A₀ d) (σ : ℝ) : Lp ℝ 2 (gam d) := (memLp_Gm hφ σ).toLp (Gm φ σ)

/-- the generator applied to the Mehler flow, as an `L²(γ)` class -/
noncomputable def DQcls (hφ : φ ∈ A₀ d) (σ : ℝ) : Lp ℝ 2 (gam d) :=
  (memLp_Lou_Gm hφ σ).toLp (Lou (Gm φ σ))

/-- **strong `L²(γ)` derivative of the Mehler flow**: `d/ds [Gm φ s] = [Lou (Gm φ s)]` for `s > 0`. -/
theorem hasDerivAt_Qcls (hφ : φ ∈ A₀ d) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Qcls hφ) (DQcls hφ s) s := by
  obtain ⟨K, hK0, hK⟩ := abs_Lou_Gm_le hφ
  refine hasDerivAt_toLp (μ := gam d) (G := Gm φ) (D := Lou (Gm φ s))
    (bnd := fun x => K * (1 + ‖x‖)) (memLp_Gm hφ) (memLp_Lou_Gm hφ s)
    (integrable_sq_mul_one_add_norm K) ?_ ?_ ?_
  · exact ae_of_all _ fun x => hasDerivAt_Mh_time hφ x hs
  · filter_upwards [Ioi_mem_nhds hs] with σ hσ
    refine ae_of_all _ fun x => ?_
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
      (f := fun σ => Gm φ σ x) (f' := fun σ => Lou (Gm φ σ) x) (s := Set.Ioi 0)
      (C := K * (1 + ‖x‖)) (x := s) (y := σ)
      (fun τ hτ => (hasDerivAt_Mh_time hφ x (Set.mem_Ioi.1 hτ)).hasDerivWithinAt)
      (fun τ hτ => by
        rw [Real.norm_eq_abs]; exact hK τ (le_of_lt (Set.mem_Ioi.1 hτ)) x)
      (convex_Ioi 0) hs hσ
    simpa [Real.norm_eq_abs] using h
  · exact ae_of_all _ fun x => hK s hs.le x

/-- the Mehler flow is continuous into `L²(γ)` (at every time; at `0` its value is `[φ]`) -/
theorem continuous_Qcls (hφ : φ ∈ A₀ d) : Continuous (Qcls hφ) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  obtain ⟨C, hC⟩ := bdd_of_A₀ hφ
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine continuousAt_toLp (μ := gam d) (G := Gm φ) (bnd := fun _ => C) (memLp_Gm hφ)
    (by simp) (ae_of_all _ fun x => ?_)
    (fun σ => ae_of_all _ fun x => abs_Mh_le hC _ _ x)
  have : Continuous fun σ : ℝ => ∫ z, φ (aa σ • x + cc σ • z) ∂(gam d) := by
    refine continuous_of_dominated (μ := gam d) (bound := fun _ => C)
      (fun σ => ((smooth hφ).continuous.comp (by
        have := continuous_aa; have := continuous_cc; fun_prop)).aestronglyMeasurable)
      (fun σ => ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _) (integrable_const C)
      (ae_of_all _ fun z => (smooth hφ).continuous.comp (by
        have := continuous_aa; have := continuous_cc; fun_prop))
  exact this.continuousAt

end MarkovTriple.Stochastic.R30
