import Mathlib
import MarkovTriple.Frozen.FullMarkovTriple
import MarkovTriple.Hilbert.FullBridge

/-! # Bakry–Émery (Phase 4b), part 1: one-variable chain rule on `𝒜`

`FullMarkovTriple.diffusion_A` is stated for `ψ : (Fin k → ℝ) → ℝ`.  For `k = 1` and `ψ = φ ∘ (· 0)`
we record the usual form of the chain rule with `deriv φ`, `deriv (deriv φ)`. -/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E]

/-- `φ` viewed as a function on `Fin 1 → ℝ`. -/
def lift (φ : ℝ → ℝ) : (Fin 1 → ℝ) → ℝ := fun z => φ (z 0)

lemma contDiff_lift {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (lift φ) :=
  hφ.comp (contDiff_apply ℝ ℝ 0)

lemma pderiv_lift {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : Fin 1 → ℝ) :
    pderiv (lift φ) 0 z = deriv φ (z 0) := by
  have h1 : HasDerivAt φ (deriv φ (z 0)) (z 0) :=
    ((hφ.differentiable (by simp)) _).hasDerivAt
  have h2 := h1.comp_hasFDerivAt z
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  unfold pderiv
  have e : fderiv ℝ (lift φ) z = deriv φ (z 0) • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 1 => ℝ) 0 := h2.fderiv
  rw [e]
  simp

lemma pderiv_lift_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    pderiv (lift φ) 0 = lift (deriv φ) := by
  funext z; exact pderiv_lift hφ z

lemma contDiff_deriv' {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv φ) :=
  (contDiff_infty_iff_deriv.1 hφ).2

lemma pderiv₂_lift {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : Fin 1 → ℝ) :
    pderiv₂ (lift φ) 0 0 z = deriv (deriv φ) (z 0) := by
  unfold pderiv₂
  rw [pderiv_lift_eq hφ]
  exact pderiv_lift (contDiff_deriv' hφ) z

variable (F : FullMarkovTriple E)

lemma comp_mem_A {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {f : E → ℝ} (hf : f ∈ F.A) :
    (fun x => φ (f x)) ∈ F.A :=
  F.A_comp 1 (lift φ) (contDiff_lift hφ) (fun _ => f) (fun _ => hf)

lemma Γ_comp {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {f : E → ℝ} (hf : f ∈ F.A)
    {g : E → ℝ} (hg : g ∈ F.A) :
    F.Γ (fun x => φ (f x)) g = fun x => deriv φ (f x) * F.Γ f g x := by
  have h := ((F.diffusion_A 1 (lift φ) (contDiff_lift hφ) (fun _ => f) (fun _ => hf)).1 g hg)
  rw [show (fun x => φ (f x)) = fun x => lift φ (fun i => (fun _ => f) i x) from rfl, h]
  funext x
  simp [pderiv_lift hφ]

lemma L_comp {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {f : E → ℝ} (hf : f ∈ F.A) :
    F.L (fun x => φ (f x)) =
      fun x => deriv φ (f x) * F.L f x + deriv (deriv φ) (f x) * F.Γ f f x := by
  have h := ((F.diffusion_A 1 (lift φ) (contDiff_lift hφ) (fun _ => f) (fun _ => hf)).2)
  rw [show (fun x => φ (f x)) = fun x => lift φ (fun i => (fun _ => f) i x) from rfl, h]
  funext x
  simp [pderiv_lift hφ, pderiv₂_lift hφ]

end MarkovTriple.BE
