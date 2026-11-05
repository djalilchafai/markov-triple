import Mathlib
import MarkovTriple.Stochastic.R32B2.Weak
import MarkovTriple.Stochastic.R31U.Reverse
import MarkovTriple.BGL.Theory.GradientBound

/-!
# Round 32 (B2), part 3: the pointwise reverse Poincaré inequality (B2)

`2t Γ(P_t f) ≤ P_t(f²) − (P_t f)²` a.e. for `f ∈ 𝒜₀`, finite `μ`, `CD(0,∞)` (BGL; interpolation `Θ(r) = ∫ P_r h (P_{t-r} f)²`).
`Θ'(s) = 2 ∫ P_s h Γ(P_{t-s} f) ≥ 2 ∫ h Γ(P_t f)` by `weak_mono`, so `Θ(t) - Θ(0) ≥ 2t ∫ h Γ(P_t f)`; since `f² ∈ 𝒜₀`, `P_t(f²)` has an
`𝒜`-representative and the ordinary positivity detection F2 concludes.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Stochastic.R32B2

open MarkovTriple.BGL MarkovTriple.BGL.FullTriple MarkovTriple.Stochastic.R31U

/-- integrated form: `∫ h (P_t(f²) − (P_t f)² − 2tΓ(P_t f)) ≥ 0` for `0 ≤ h ∈ 𝒜₀` -/
lemma reverse_integrated {E : Type*} [MeasurableSpace E] (T : FullTriple E) [IsFiniteMeasure T.μ]
    (hCD : T.CD 0 ∞) (f h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) (t : ℝ≥0) :
    2 * (t : ℝ) * ∫ x, h.1 x * G T (T.Pt t f) (T.Pt t f) x ∂T.μ ≤
      ∫ x, h.1 x * T.Pt t ⟨f.1 * f.1, T.A₀.mul_mem f.2 f.2⟩ x ∂T.μ -
        ∫ x, h.1 x * (T.Pt t f x) ^ 2 ∂T.μ := by
  set c : ℝ := 2 * ∫ x, h.1 x * G T (T.Pt t f) (T.Pt t f) x ∂T.μ with hc
  have hmonoΘ : MonotoneOn (fun r => theta T f h t r - c * r) (Icc 0 (t : ℝ)) := by
    have hd : ∀ s ∈ Ioo (0 : ℝ) (t : ℝ), HasDerivAt (fun r => theta T f h t r - c * r) (2 * ∫ x, T.Pt s.toNNReal h x *
          T.toDiffusionTriple.ΓA (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ
          - c) s := by
      intro s hs
      have hd0 := (theta_hasDerivAt hCD f h t hs).sub ((hasDerivAt_id s).const_mul c)
      simp only [id, mul_one] at hd0
      exact hd0
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact ((theta_continuous f h t).sub (continuous_const.mul continuous_id)).continuousOn
    · rw [interior_Icc]
      intro s hs
      exact (hd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hd s hs).deriv]
      have := weak_mono hCD f h hh t hs
      rw [hc]; linarith
  have h10 := hmonoΘ (a := 0) (b := (t : ℝ)) ⟨le_rfl, t.2⟩ ⟨t.2, le_rfl⟩ t.2
  simp only [mul_zero, sub_zero] at h10
  -- identification of the end points
  set f2 : T.A₀ := ⟨f.1 * f.1, T.A₀.mul_mem f.2 f.2⟩ with hf2
  have hΘ0 : theta T f h t 0 = ∫ x, h.1 x * (T.Pt t f x) ^ 2 ∂T.μ := by
    unfold theta
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple h, T.Pt_ae t f] with x h1 h2
    have e1 : (T.orb h 0 : E → ℝ) x = h.1 x := by rw [T.orb_zero]; exact h1
    have e2 : (T.orb f ((t : ℝ) - 0) : E → ℝ) x = T.Pt t f x := by
      simpa [FullTriple.orb] using h2
    rw [e1, e2]; ring
  have hΘt : theta T f h t t = ∫ x, h.1 x * T.Pt t f2 x ∂T.μ := by
    unfold theta
    rw [← integral_Pt_mul T t h f2]
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple f, T.Pt_ae t h] with x h1 h2
    have e1 : (T.orb f ((t : ℝ) - t) : E → ℝ) x = f.1 x := by rw [sub_self, T.orb_zero]; exact h1
    have e2 : (T.orb h t : E → ℝ) x = T.Pt t h x := by
      simpa [FullTriple.orb] using h2
    rw [e1, e2]; simp only [hf2, Pi.mul_apply]; ring
  rw [hΘ0, hΘt] at h10
  rw [hc] at h10
  nlinarith [h10]

/-- **B2 (frozen statement): the pointwise reverse Poincaré inequality.** -/
theorem reverse_poincare_pointwise {E : Type*} [MeasurableSpace E] (T : FullTriple E)
    [IsFiniteMeasure T.μ] (hCD : T.CD 0 ∞) (f : T.A₀) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ x ∂T.μ, 2 * (t : ℝ) * T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) x ≤
      T.Pt t ⟨f.1 * f.1, T.A₀.mul_mem f.2 f.2⟩ x - (T.Pt t f x) ^ 2 := by
  have _ := ht
  set f2 : T.A₀ := ⟨f.1 * f.1, T.A₀.mul_mem f.2 f.2⟩ with hf2
  have hΓ : G T (T.Pt t f) (T.Pt t f) ∈ T.A := G_mem (T.Pt_mem_A t f) (T.Pt_mem_A t f)
  have hsq : (fun x => (T.Pt t f x) ^ 2) ∈ T.A := by
    have := T.A.mul_mem (T.Pt_mem_A t f) (T.Pt_mem_A t f)
    have e : (fun x => (T.Pt t f x) ^ 2) = T.Pt t f * T.Pt t f := by funext x; simp [sq]
    rw [e]; exact this
  set u : E → ℝ := fun x => T.Pt t f2 x - (T.Pt t f x) ^ 2 - 2 * (t : ℝ) * G T (T.Pt t f) (T.Pt t f) x with hu
  have huA : u ∈ T.A := by
    refine T.A.sub_mem (T.A.sub_mem (T.Pt_mem_A t f2) hsq) ?_
    have := T.A.smul_mem hΓ (2 * (t : ℝ))
    have e : (fun x => 2 * (t : ℝ) * G T (T.Pt t f) (T.Pt t f) x) = (2 * (t : ℝ)) • G T (T.Pt t f) (T.Pt t f) := by
      funext x; simp [smul_eq_mul]
    rw [e]; exact this
  have hpos : 0 ≤ᵐ[T.μ] u := by
    refine T.pos_detect u huA (fun h hh h0 => ?_)
    set h' : T.A₀ := ⟨h, hh⟩
    have key := reverse_integrated T hCD f h' h0 t
    have i1 : Integrable (fun x => h x * T.Pt t f2 x) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal _ (T.Pt_mem_A t f2) h hh)
    have i2 : Integrable (fun x => h x * (T.Pt t f x) ^ 2) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal _ hsq h hh)
    have i3 : Integrable (fun x => h x * G T (T.Pt t f) (T.Pt t f) x) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal _ hΓ h hh)
    have e : (fun x => h x * u x) = fun x => h x * T.Pt t f2 x - h x * (T.Pt t f x) ^ 2 -
        2 * (t : ℝ) * (h x * G T (T.Pt t f) (T.Pt t f) x) := by
      funext x; simp only [hu]; ring
    have i12 : Integrable (fun x => h x * T.Pt t f2 x - h x * (T.Pt t f x) ^ 2) T.μ := i1.sub i2
    rw [e, integral_sub i12 (i3.const_mul _), integral_sub i1 i2, integral_const_mul]
    show 0 ≤ _
    simp only [h'] at key
    linarith
  filter_upwards [hpos] with x hx
  simp only [hu, Pi.zero_apply] at hx
  show 2 * (t : ℝ) * G T (T.Pt t f) (T.Pt t f) x ≤ _
  linarith

end MarkovTriple.Stochastic.R32B2
