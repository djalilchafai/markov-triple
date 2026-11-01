import MarkovTriple.BGL.Instances.OU.LSIMain

/-! Round-9 audit: unfold `ouFull_gradient_bound` to the concrete Mehler statement. NOT imported. -/
open MeasureTheory ProbabilityTheory
open MarkovTriple.BGL.Instances.OU

namespace MarkovTriple.BGL.Audit.GradUnfold

/-- Concrete form: for `f ∈ C_c^∞`, a.e. `x`,
`(e^{-t} ∫ f'(e^{-t}x + c y) dγ(y))² ≤ e^{-2t} ∫ f'(e^{-t}x + c y)² dγ(y)`, `c = √(1-e^{-2t})`. -/
theorem concrete_grad (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (t : NNReal) :
    ∀ᵐ x ∂(gaussianReal 0 1),
      (Real.exp (-(t:ℝ)) * ∫ y, deriv f (Real.exp (-(t:ℝ)) * x + √(1 - Real.exp (-(t:ℝ)) ^ 2) * y)
          ∂(gaussianReal 0 1)) ^ 2 ≤
      Real.exp (-2 * 1 * (t:ℝ)) * ∫ y, (deriv f (Real.exp (-(t:ℝ)) * x +
          √(1 - Real.exp (-(t:ℝ)) ^ 2) * y)) ^ 2 ∂(gaussianReal 0 1) := by
  let φ : ouFull.A₀ := ⟨f, hf, hc⟩
  have h := ouFull_gradient_bound φ t
  have hc' : (⟨ouFull.toDiffusionTriple.ΓA φ.1 φ.1, ouFull.ΓA_self_mem_A₀ φ.2⟩ : ouFull.A₀).1 =
      fun x => deriv f x * deriv f x := by
    show ouDiff.ΓA f f = _
    rw [ouDiff_ΓA hf hf]; rfl
  have hP := Pt_eq_Uf φ t
  have hΓ : ouFull.toDiffusionTriple.ΓA (ouFull.Pt t φ) (ouFull.Pt t φ) =
      fun x => m1 f t x * m1 f t x := by
    rw [hP]
    exact ΓA_eq_of_hasDeriv (sm_m0 φ.2 _) (d0x φ.2 _)
  set c : ouFull.A₀ := ⟨ouFull.toDiffusionTriple.ΓA φ.1 φ.1, ouFull.ΓA_self_mem_A₀ φ.2⟩ with hcdef
  have hae := ouFull.Pt_ae t c
  have hPc := Pt_eq_Uf c t
  rw [hΓ] at h
  filter_upwards [h, hae] with x hx hx2
  rw [hx2, hPc, show c.1 = _ from hc'] at hx
  have e1 : m1 f t x * m1 f t x = (Real.exp (-(t:ℝ)) * ∫ y, deriv f (Real.exp (-(t:ℝ)) * x +
      √(1 - Real.exp (-(t:ℝ)) ^ 2) * y) ∂(gaussianReal 0 1)) ^ 2 := by
    simp only [m1, Uf, ea, ec, MarkovTriple.Sanity.OU.Mh, sq]
  have e2 : Uf (fun x => deriv f x * deriv f x) (t:ℝ) x = ∫ y, (deriv f (Real.exp (-(t:ℝ)) * x +
      √(1 - Real.exp (-(t:ℝ)) ^ 2) * y)) ^ 2 ∂(gaussianReal 0 1) := by
    simp only [Uf, ea, ec, MarkovTriple.Sanity.OU.Mh, sq]
  simpa [e1, e2] using hx

#print axioms concrete_grad
end MarkovTriple.BGL.Audit.GradUnfold
