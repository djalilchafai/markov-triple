import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Diffusion

/-!
# Gibbs measures: integration by parts against smooth (non compactly supported) functions

Ingredient of the book's route to essential self-adjointness (BGL Prop. 3.2.1 / 3.3.11) and
ergodicity (Prop. 3.3.10): for `f ∈ 𝒜 = C^∞(ℝ)` and `g ∈ 𝒜₀`, `∫ g L f dμ = -∫ g' f' dμ`
(the F7 identity on `𝒜`, here for the Gibbs generator `L f = f'' - V' f'`), and the fact that a
smooth function satisfying the weak equation `∫ f L a dμ = λ ∫ f a dμ` (`a ∈ 𝒜₀`, i.e. `L* f = λ f`
in the sense of BGL Def. 3.1.9) satisfies `L f = λ f` pointwise.
-/

open MeasureTheory Filter Topology
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- Integration by parts `∫ g L f dμ = -∫ g' f' dμ` for smooth `f, g`, one of them compactly
supported (F7 on `𝒜 = C^∞` for the Gibbs generator). -/
lemma ibp_sm {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g)
    (hc : HasCompactSupport g ∨ HasCompactSupport f) :
    ∫ x, g x * Lg G.V f x ∂G.μ = -∫ x, deriv g x * deriv f x ∂G.μ := by
  have hgf : HasCompactSupport (fun x => g x * deriv f x) := by
    rcases hc with h | h
    · exact h.mul_right
    · exact h.deriv.mul_left
  have hm := G.ibp_master hf hg hgf
  have c1 : HasCompactSupport (fun x => g x * Lg G.V f x) := by
    rcases hc with h | h
    · exact h.mul_right
    · have : HasCompactSupport (Lg G.V f) := by
        have h2 : HasCompactSupport (fun x => deriv G.V x * deriv f x) := h.deriv.mul_left
        exact h.deriv.deriv.sub h2
      exact this.mul_left
  have c2 : HasCompactSupport (fun x => deriv g x * deriv f x) := by
    rcases hc with h | h
    · exact h.deriv.mul_right
    · exact h.deriv.mul_left
  have i1 : Integrable (fun x => G.w x * (g x * Lg G.V f x)) volume :=
    G.integrable_cs (hg.continuous.mul (sm_Lg G.smooth hf).continuous) c1
  have i2 : Integrable (fun x => G.w x * (deriv g x * deriv f x)) volume :=
    G.integrable_cs (hg.deriv'.continuous.mul hf.deriv'.continuous) c2
  simp only [mul_add] at hm
  rw [integral_add i1 i2] at hm
  rw [G.integral_μ, G.integral_μ]
  linarith

/-- Weak equation `L* f = λ f` (against `𝒜₀`, BGL Def. 3.1.9) for a smooth `f` forces `L f = λ f`
pointwise. -/
lemma Lg_eq_of_weak {f : ℝ → ℝ} (hf : Sm f) (lam : ℝ)
    (h : ∀ a ∈ OA₀, ∫ x, f x * Lg G.V a x ∂G.μ = lam * ∫ x, f x * a x ∂G.μ) :
    ∀ x, Lg G.V f x = lam * f x := by
  set H : ℝ → ℝ := fun x => Lg G.V f x - lam * f x with hH
  have hHc : Continuous H :=
    (sm_Lg G.smooth hf).continuous.sub (continuous_const.mul hf.continuous)
  have key : ∀ a ∈ OA₀, ∫ x, G.w x * (a x * H x) = 0 := by
    intro a ha
    have e1 := G.ibp_sm (f := a) (g := f) ha.1 hf (Or.inr ha.2)
    have e2 := G.ibp_sm (f := f) (g := a) hf ha.1 (Or.inl ha.2)
    have hw := h a ha
    have i1 : Integrable (fun x => G.w x * (a x * Lg G.V f x)) volume :=
      G.integrable_cs (ha.1.continuous.mul (sm_Lg G.smooth hf).continuous) ha.2.mul_right
    have i2 : Integrable (fun x => G.w x * (a x * (lam * f x))) volume :=
      G.integrable_cs (ha.1.continuous.mul (continuous_const.mul hf.continuous)) ha.2.mul_right
    have e3 : ∫ x, G.w x * (a x * H x) =
        (∫ x, G.w x * (a x * Lg G.V f x)) - ∫ x, G.w x * (a x * (lam * f x)) := by
      rw [← integral_sub i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hH]; ring
    have e4 : ∫ x, G.w x * (a x * (lam * f x)) = lam * ∫ x, f x * a x ∂G.μ := by
      rw [G.integral_μ, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      ring
    have e5 : ∫ x, G.w x * (a x * Lg G.V f x) = ∫ x, a x * Lg G.V f x ∂G.μ := by
      rw [G.integral_μ]
    have e6 : ∫ x, deriv a x * deriv f x ∂G.μ = ∫ x, deriv f x * deriv a x ∂G.μ :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [e3, e4, e5, e2, ← hw, e1, e6]
    ring
  have hloc : LocallyIntegrable (fun x => G.w x * H x) volume :=
    (G.w_smooth.continuous.mul hHc).locallyIntegrable
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg hgc => by
    have := key g ⟨hg, hgc⟩
    simp only [smul_eq_mul]
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring)
  have hcont : Continuous (fun x => G.w x * H x) := G.w_smooth.continuous.mul hHc
  have hz : ∀ x, G.w x * H x = 0 := by
    have := (hcont.ae_eq_iff_eq volume continuous_const (f := fun x => G.w x * H x)
      (g := fun _ => (0 : ℝ))).1 hae
    exact fun x => congrFun this x
  intro x
  have := hz x
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 (G.w_pos x).ne'
  · simp only [hH] at h0; linarith

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
