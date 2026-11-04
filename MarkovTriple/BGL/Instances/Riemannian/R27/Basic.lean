import Mathlib
import MarkovTriple.BGL.Frozen.PartialDeriv
import MarkovTriple.BGL.Instances.Riemannian.R26.ChartChange

/-!
# Round 27 J: common definitions and a small calculus toolkit for `pderiv`

`jac`, `Gch`, `Lch` (chartwise Jacobian, carré du champ, Laplace-Beltrami in coordinates, BGL Appendix C.3) and
the derivative of a determinant of a differentiable matrix field (Jacobi's formula in the form
`∂ₖ det M = Σₘ det (M with row m replaced by ∂ₖ row m)`).
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

abbrev Ev (d : ℕ) := Fin d → ℝ

/-- the Jacobian matrix `J a b = ∂_b τ_a` -/
noncomputable def jac {d : ℕ} (τ : Ev d → Ev d) (x : Ev d) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => pderiv (fun y => τ y a) b x

/-- chartwise carré du champ `Σ g^{ij} ∂ᵢF ∂ⱼH` -/
noncomputable def Gch {d : ℕ} (g : Fin d → Fin d → Ev d → ℝ) (F H : Ev d → ℝ) (x : Ev d) : ℝ :=
  ∑ i, ∑ j, g i j x * pderiv F i x * pderiv H j x

/-- chartwise Laplace-Beltrami `(1/w) Σᵢ ∂ᵢ (w Σⱼ g^{ij} ∂ⱼ F)` -/
noncomputable def Lch {d : ℕ} (g : Fin d → Fin d → Ev d → ℝ) (w : Ev d → ℝ) (F : Ev d → ℝ) (x : Ev d) : ℝ :=
  (w x)⁻¹ * ∑ i, pderiv (fun y => w y * ∑ j, g i j y * pderiv F j y) i x

section pderiv_calculus
variable {d : ℕ} {f g : Ev d → ℝ} {x : Ev d}

lemma pderiv_eq_of_hasFDerivAt {f' : Ev d →L[ℝ] ℝ} (h : HasFDerivAt f f' x) (k : Fin d) :
    pderiv f k x = f' (Pi.single k 1) := by
  unfold pderiv; rw [h.fderiv]

lemma pderiv_congr_eventually (h : f =ᶠ[𝓝 x] g) (k : Fin d) : pderiv f k x = pderiv g k x := by
  unfold pderiv; rw [h.fderiv_eq]

lemma pderiv_add (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (k : Fin d) :
    pderiv (fun y => f y + g y) k x = pderiv f k x + pderiv g k x := by
  have h := pderiv_eq_of_hasFDerivAt (f := fun y => f y + g y) (hf.hasFDerivAt.add hg.hasFDerivAt) k
  rw [h]; rfl

lemma pderiv_sub (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (k : Fin d) :
    pderiv (fun y => f y - g y) k x = pderiv f k x - pderiv g k x := by
  have h := pderiv_eq_of_hasFDerivAt (f := fun y => f y - g y) (hf.hasFDerivAt.sub hg.hasFDerivAt) k
  rw [h]; rfl

lemma pderiv_mul (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (k : Fin d) :
    pderiv (fun y => f y * g y) k x = f x * pderiv g k x + g x * pderiv f k x := by
  have h := pderiv_eq_of_hasFDerivAt (f := fun y => f y * g y) (hf.hasFDerivAt.mul hg.hasFDerivAt) k
  rw [h]
  simp [smul_eq_mul, pderiv]

lemma pderiv_const_mul (c : ℝ) (k : Fin d) : pderiv (fun y : Ev d => c * f y) k x = c * pderiv f k x := by
  by_cases h : DifferentiableAt ℝ f x
  · rw [pderiv_eq_of_hasFDerivAt (h.hasFDerivAt.const_mul c)]; rfl
  · by_cases hc : c = 0
    · subst hc; simp [pderiv]
    · have h' : ¬ DifferentiableAt ℝ (fun y : Ev d => c * f y) x := fun h2 => h (by
        have := h2.const_mul c⁻¹
        simpa [← mul_assoc, inv_mul_cancel₀ hc] using this)
      simp [pderiv, fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']

lemma pderiv_const (c : ℝ) (k : Fin d) : pderiv (fun _ : Ev d => c) k x = 0 := by
  unfold pderiv; simp

lemma pderiv_neg (k : Fin d) : pderiv (fun y : Ev d => -f y) k x = -pderiv f k x := by
  have := pderiv_const_mul (f := f) (x := x) (-1) k
  simpa using this

lemma pderiv_sum {ι : Type*} (s : Finset ι) {F : ι → Ev d → ℝ} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x)
    (k : Fin d) : pderiv (fun y => ∑ i ∈ s, F i y) k x = ∑ i ∈ s, pderiv (F i) k x := by
  unfold pderiv; rw [fderiv_fun_sum hF]; simp

lemma pderiv_coord (i k : Fin d) (x : Ev d) : pderiv (fun y : Ev d => y i) k x = if i = k then 1 else 0 := by
  have h : HasFDerivAt (fun y : Ev d => y i) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x :=
    hasFDerivAt_apply i x
  rw [pderiv_eq_of_hasFDerivAt h]
  simp [Pi.single_apply]

end pderiv_calculus

section det_deriv

variable {d : ℕ}

/-- the determinant as a continuous multilinear map of the rows -/
noncomputable def detCM (d : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin d => Fin d → ℝ) ℝ where
  toMultilinearMap := (Matrix.detRowAlternating : (Fin d → ℝ) [⋀^Fin d]→ₗ[ℝ] ℝ).toMultilinearMap
  cont := by
    have : Continuous fun r : Fin d → Fin d → ℝ => (Matrix.of r).det :=
      Continuous.matrix_det continuous_id
    exact this

lemma detCM_apply (M : Matrix (Fin d) (Fin d) ℝ) : detCM d (fun m => M m) = M.det := rfl

lemma differentiableAt_det (M : Ev d → Matrix (Fin d) (Fin d) ℝ) (x : Ev d)
    (hM : ∀ a b, DifferentiableAt ℝ (fun y => M y a b) x) :
    DifferentiableAt ℝ (fun y => (M y).det) x := by
  have hrows : DifferentiableAt ℝ
      (fun y => (fun m => (fun b => M y m b : Fin d → ℝ) : Fin d → Fin d → ℝ)) x :=
    differentiableAt_pi.2 fun m => differentiableAt_pi.2 fun b => hM m b
  have hD := (detCM d).hasFDerivAt (fun m => (fun b => M x m b : Fin d → ℝ))
  exact (hD.comp x hrows.hasFDerivAt).differentiableAt

/-- **Jacobi's formula** `∂ₖ det M = Σₘ det (M with row m replaced by ∂ₖ row m)`. -/
lemma pderiv_det (M : Ev d → Matrix (Fin d) (Fin d) ℝ) (x : Ev d)
    (hM : ∀ a b, DifferentiableAt ℝ (fun y => M y a b) x) (k : Fin d) :
    pderiv (fun y => (M y).det) k x =
      ∑ m, (Matrix.updateRow (M x) m (fun b => pderiv (fun y => M y m b) k x)).det := by
  classical
  have hrow : ∀ m, DifferentiableAt ℝ (fun y => (fun b => M y m b : Fin d → ℝ)) x := fun m =>
    differentiableAt_pi.2 fun b => hM m b
  have hrows : DifferentiableAt ℝ (fun y => (fun m => (fun b => M y m b : Fin d → ℝ) : Fin d → Fin d → ℝ)) x :=
    differentiableAt_pi.2 hrow
  have hD := (detCM d).hasFDerivAt (fun m => (fun b => M x m b : Fin d → ℝ))
  have hh : HasFDerivAt (fun y => (fun m => (fun b => M y m b : Fin d → ℝ) : Fin d → Fin d → ℝ))
      (ContinuousLinearMap.pi fun m => ContinuousLinearMap.pi fun b => fderiv ℝ (fun y => M y m b) x) x := by
    rw [hasFDerivAt_pi']; intro m; rw [hasFDerivAt_pi']; intro b
    simpa using (hM m b).hasFDerivAt
  have hcomp := hD.comp x hh
  have e : (fun y => (M y).det) = (detCM d) ∘ (fun y => (fun m => (fun b => M y m b : Fin d → ℝ) : Fin d → Fin d → ℝ)) := rfl
  rw [e, pderiv_eq_of_hasFDerivAt hcomp]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← detCM_apply]
  congr 1

end det_deriv

end MarkovTriple.BGL.Instances.Riemannian.R27
