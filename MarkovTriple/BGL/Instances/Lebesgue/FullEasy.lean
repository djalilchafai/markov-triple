import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Diffusion

/-!
# The elementary fields F1–F7, F9 of the Brownian full triple on `(ℝ, Lebesgue)`
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

lemma ΓA_eq_Gf {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) : lebesgueDiffusion.ΓA f g = Gf f g := by
  funext x
  show (Lf (f * g) x - f x * Lf g x - g x * Lf f x) / 2 = Gf f g x
  rw [Lf_mul hf hg x]
  simp only [Gf]
  ring

lemma L_eq : lebesgueDiffusion.L = Lf := rfl

/-- F1. -/
lemma F1 {f : ℝ → ℝ} (hf : f ∈ A) {h : ℝ → ℝ} (hh : h ∈ A₀) : h * f ∈ A₀ :=
  mem_A₀.2 ⟨(smooth hh).mul hf, (cs hh).mul_right⟩

/-- F2. -/
lemma F2 {f : ℝ → ℝ} (hf : f ∈ A)
    (h : ∀ h ∈ A₀, 0 ≤ᵐ[volume] h → 0 ≤ ∫ x, h x * f x) : 0 ≤ᵐ[volume] f := by
  have hfc : Continuous f := (mem_A.1 hf).continuous
  have hall : ∀ x, 0 ≤ f x := by
    intro x0
    by_contra hneg
    push Not at hneg
    have hopen : IsOpen {x | f x < 0} := isOpen_lt hfc continuous_const
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen x0 hneg
    let b : ContDiffBump x0 := ⟨r / 2, r, by positivity, by linarith⟩
    have hb0 : ∀ x, 0 ≤ b x := fun x => b.nonneg
    have hbm : (fun x => b x) ∈ A₀ := mem_A₀.2 ⟨b.contDiff, b.hasCompactSupport⟩
    have hneg' : ∀ x, b x * f x ≤ 0 := by
      intro x
      by_cases hx : x ∈ Metric.ball x0 r
      · exact mul_nonpos_of_nonneg_of_nonpos (hb0 x) (hball hx).le
      · have : b x = 0 := b.zero_of_le_dist (by simpa [Metric.mem_ball, not_lt, dist_comm] using hx)
        simp [this]
    have hpos : 0 < ∫ x, -(b x * f x) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x0)
        ((b.continuous.mul hfc).neg) ?_ (fun x => by simpa using hneg' x) ?_
      · exact (b.hasCompactSupport.mul_right).neg
      · have h1 : 0 < b x0 := b.pos_of_mem_ball (Metric.mem_ball_self b.rOut_pos)
        have h2 : f x0 < 0 := hneg
        have : b x0 * f x0 < 0 := mul_neg_of_pos_of_neg h1 h2
        simpa using this.ne
    have := h _ hbm (Filter.Eventually.of_forall hb0)
    rw [integral_neg] at hpos
    linarith
  exact Filter.Eventually.of_forall hall

lemma A_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ A) : (fun x => ψ (fun i => f i x)) ∈ A :=
  comp_sm ψ hψ f hf

lemma L_mem_A {f : ℝ → ℝ} (hf : f ∈ A) : Lf f ∈ A := Sm.deriv' (Sm.deriv' (mem_A.1 hf))

lemma F5 {f : ℝ → ℝ} (hf : f ∈ A) : 0 ≤ᵐ[volume] lebesgueDiffusion.ΓA f f := by
  rw [ΓA_eq_Gf hf hf]
  exact Filter.Eventually.of_forall fun x => by simpa [Gf] using mul_self_nonneg (deriv f x)

lemma F6Γ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ A) {g : ℝ → ℝ} (hg : g ∈ A) :
    lebesgueDiffusion.ΓA (fun x => ψ (fun i => f i x)) g =ᵐ[volume]
      fun x => ∑ i, pderiv ψ i (fun j => f j x) * lebesgueDiffusion.ΓA (f i) g x := by
  refine Filter.Eventually.of_forall fun x => ?_
  rw [ΓA_eq_Gf (comp_sm ψ hψ f hf) hg]
  have := congrFun ((diffusion_c k ψ hψ f hf).1 g) x
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by rw [ΓA_eq_Gf (hf i) hg]

lemma F6L (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ A) :
    Lf (fun x => ψ (fun i => f i x)) =ᵐ[volume]
      fun x => ∑ i, pderiv ψ i (fun j => f j x) * Lf (f i) x +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * lebesgueDiffusion.ΓA (f i) (f j) x := by
  refine Filter.Eventually.of_forall fun x => ?_
  have := congrFun (diffusion_c k ψ hψ f hf).2 x
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ΓA_eq_Gf (hf i) (hf j)]

lemma F7 {f g : ℝ → ℝ} (hf : f ∈ A) (hg : g ∈ A₀) :
    ∫ x, lebesgueDiffusion.ΓA f g x = -∫ x, g x * Lf f x ∧
      ∫ x, lebesgueDiffusion.ΓA f g x = -∫ x, f x * Lf g x := by
  rw [ΓA_eq_Gf hf (smooth hg)]
  exact ⟨by rw [ibp_L hf hg]; simp, by rw [ibp_L' hf hg]; simp⟩

lemma F9 {f : ℝ → ℝ} (hf : f ∈ A) (h0 : lebesgueDiffusion.ΓA f f =ᵐ[volume] 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  have hf' := mem_A.1 hf
  rw [ΓA_eq_Gf hf' hf'] at h0
  have h1 : deriv f =ᵐ[volume] 0 := by
    filter_upwards [h0] with x hx
    simp only [Gf, Pi.zero_apply] at hx
    exact mul_self_eq_zero.1 hx
  have h2 : deriv f = 0 :=
    (Continuous.ae_eq_iff_eq volume (Sm.deriv' hf').continuous continuous_const).1 h1
  have h3 : ∀ x, deriv f x = 0 := fun x => congrFun h2 x
  have := is_const_of_deriv_eq_zero (hf'.differentiable (by simp)) h3
  exact ⟨f 0, Filter.Eventually.of_forall fun x => this x 0⟩

end MarkovTriple.BGL.Lebesgue
