import Mathlib
import MarkovTriple.BGL.Analysis.Circle.Basic

/-!
# One-dimensional charts of the circle: chartwise `Γ`, `L` from `(g, w)`, coordinate invariance

BGL Sect. 1.11.3 / Appendix C.3 in dimension `d = 1`: a chart is a smooth increasing lift `x : ℝ → ℝ` of an open arc of
`𝕋 = ℝ/ℤ` (`pt t = x t mod 1`), with co-metric `g = (x')⁻²` and Riemannian density `w = g^{-1/2} = x'` (`w_g = det(g)^{-1/2}`);
the chartwise carré du champ is `Γ(f,h) = g F' H'` and the chartwise Laplace–Beltrami operator
`L f = (1/w)(w g F')'` with `F = f ∘ pt`.  We prove they agree with the intrinsic `Gc`, `Lc` of the library circle on `𝒜₀`
(coordinate invariance), compute the stereographic charts and the transition-map formulas.
-/

open MarkovTriple.Sanity.Circle
open scoped Real

namespace MarkovTriple.BGL.Instances.Riemannian.R26

/-- a one-dimensional chart of the circle -/
structure Chart1 where
  x : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) x
  dpos : ∀ t, 0 < deriv x t

namespace Chart1
variable (c : Chart1)

/-- the point of the circle with coordinate `t` -/
noncomputable def pt (t : ℝ) : 𝕋 := (c.x t : 𝕋)
/-- co-metric -/
noncomputable def g (t : ℝ) : ℝ := (deriv c.x t)⁻¹ ^ 2
/-- Riemannian density `w_g = g^{-1/2}` -/
noncomputable def w (t : ℝ) : ℝ := deriv c.x t
/-- chartwise carré du champ -/
noncomputable def Γ (f h : 𝕋 → ℝ) (t : ℝ) : ℝ :=
  c.g t * deriv (fun u => f (c.pt u)) t * deriv (fun u => h (c.pt u)) t
/-- chartwise Laplace–Beltrami operator `(1/w) (w g F')'` -/
noncomputable def L (f : 𝕋 → ℝ) (t : ℝ) : ℝ :=
  (c.w t)⁻¹ * deriv (fun u => c.w u * c.g u * deriv (fun v => f (c.pt v)) u) t

lemma hasDerivAt_x (t : ℝ) : HasDerivAt c.x (deriv c.x t) t :=
  ((c.smooth.differentiable (by simp)) t).hasDerivAt

/-- chain rule for lifts of `𝒜₀` functions -/
lemma deriv_lift {f : 𝕋 → ℝ} (hf : f ∈ A₀) (u : ℝ) :
    deriv (fun v => f (c.pt v)) u = D f (c.pt u) * deriv c.x u := by
  have hd : DifferentiableAt ℝ (fun y : ℝ => f (y : 𝕋)) (c.x u) :=
    ((mem_A₀.1 hf).differentiable (by simp)) _
  have h1 : HasDerivAt (fun y : ℝ => f (y : 𝕋)) (D f (c.x u : 𝕋)) (c.x u) := by
    rw [D_coe hf]; exact hd.hasDerivAt
  exact (h1.comp u (c.hasDerivAt_x u)).deriv

lemma w_pos (t : ℝ) : 0 < c.w t := c.dpos t

theorem Γ_eq {f h : 𝕋 → ℝ} (hf : f ∈ A₀) (hh : h ∈ A₀) (t : ℝ) : c.Γ f h t = Gc f h (c.pt t) := by
  have hne : deriv c.x t ≠ 0 := (c.dpos t).ne'
  simp only [Γ, g, deriv_lift c hf, deriv_lift c hh, Gc]
  field_simp

theorem L_eq {f : 𝕋 → ℝ} (hf : f ∈ A₀) (t : ℝ) : c.L f t = Lc f (c.pt t) := by
  have hfun : (fun u => c.w u * c.g u * deriv (fun v => f (c.pt v)) u) = fun u => D f (c.pt u) := by
    funext u
    have hne : deriv c.x u ≠ 0 := (c.dpos u).ne'
    simp only [w, g, deriv_lift c hf]
    field_simp
  have hD := D_mem hf
  have := deriv_lift c hD t
  unfold L
  rw [hfun, this]
  have hne : c.w t ≠ 0 := (c.w_pos t).ne'
  simp only [w] at hne ⊢
  unfold Lc
  field_simp

/-- **chart transition invariance**: two charts through the same point compute the same `Γ`, `L` -/
theorem chart_transition (a b : Chart1) {t s : ℝ} (h : a.pt t = b.pt s) {f k : 𝕋 → ℝ}
    (hf : f ∈ A₀) (hk : k ∈ A₀) : a.Γ f k t = b.Γ f k s ∧ a.L f t = b.L f s := by
  refine ⟨?_, ?_⟩
  · rw [Γ_eq a hf hk, Γ_eq b hf hk, h]
  · rw [L_eq a hf, L_eq b hf, h]

end Chart1

/-! ### Stereographic charts -/

/-- north stereographic chart: `x t = arctan t / π` -/
noncomputable def northChart : Chart1 where
  x := fun t => Real.arctan t / π
  smooth := (Real.contDiff_arctan.div_const π)
  dpos := fun t => by
    have h : HasDerivAt (fun t => Real.arctan t / π) (1 / (1 + t ^ 2) / π) t :=
      (Real.hasDerivAt_arctan t).div_const π
    rw [h.deriv]; positivity

/-- south stereographic chart: `x t = arctan t / π + 1/2` -/
noncomputable def southChart : Chart1 where
  x := fun t => Real.arctan t / π + 1 / 2
  smooth := (Real.contDiff_arctan.div_const π).add contDiff_const
  dpos := fun t => by
    have h : HasDerivAt (fun t => Real.arctan t / π + 1 / 2) (1 / (1 + t ^ 2) / π) t :=
      ((Real.hasDerivAt_arctan t).div_const π).add_const _
    rw [h.deriv]; positivity

lemma north_deriv (t : ℝ) : deriv northChart.x t = 1 / (π * (1 + t ^ 2)) := by
  have h : HasDerivAt (fun t => Real.arctan t / π) (1 / (1 + t ^ 2) / π) t :=
    (Real.hasDerivAt_arctan t).div_const π
  show deriv (fun t => Real.arctan t / π) t = _
  rw [h.deriv]; field_simp

lemma south_deriv (t : ℝ) : deriv southChart.x t = 1 / (π * (1 + t ^ 2)) := by
  have h : HasDerivAt (fun t => Real.arctan t / π + 1 / 2) (1 / (1 + t ^ 2) / π) t :=
    ((Real.hasDerivAt_arctan t).div_const π).add_const _
  show deriv (fun t => Real.arctan t / π + 1 / 2) t = _
  rw [h.deriv]; field_simp

theorem north_g (t : ℝ) : northChart.g t = π ^ 2 * (1 + t ^ 2) ^ 2 := by
  rw [Chart1.g, north_deriv]; field_simp

theorem north_w (t : ℝ) : northChart.w t = 1 / (π * (1 + t ^ 2)) := north_deriv t

theorem south_g (t : ℝ) : southChart.g t = π ^ 2 * (1 + t ^ 2) ^ 2 := by
  rw [Chart1.g, south_deriv]; field_simp

theorem south_w (t : ℝ) : southChart.w t = 1 / (π * (1 + t ^ 2)) := south_deriv t

/-- the transition map `τ(t) = -1/t` between the stereographic charts -/
theorem north_south_pt {t : ℝ} (ht : t ≠ 0) : northChart.pt t = southChart.pt (-1 / t) := by
  have e : -1 / t = -(t⁻¹) := by rw [neg_div, one_div]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold Chart1.pt
  show ((Real.arctan t / π : ℝ) : 𝕋) = ((Real.arctan (-1 / t) / π + 1 / 2 : ℝ) : 𝕋)
  rw [e, Real.arctan_neg]
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Real.arctan_inv_of_neg h]
    have : -(-(π / 2) - Real.arctan t) / π + 1 / 2 = Real.arctan t / π + 1 := by field_simp; ring
    rw [this, AddCircle.coe_add]
    have h1 : ((1 : ℝ) : 𝕋) = 0 := AddCircle.coe_period (1 : ℝ)
    rw [h1, add_zero]
  · rw [Real.arctan_inv_of_pos h]
    have : -(π / 2 - Real.arctan t) / π + 1 / 2 = Real.arctan t / π := by field_simp; ring
    rw [this]

theorem transition_g {t : ℝ} (ht : t ≠ 0) :
    southChart.g (-1 / t) = (1 / t ^ 2) ^ 2 * northChart.g t := by
  rw [south_g, north_g]
  have : 1 + (-1 / t) ^ 2 = (1 + t ^ 2) / t ^ 2 := by field_simp; ring
  rw [this]; field_simp

theorem transition_w {t : ℝ} (ht : t ≠ 0) :
    northChart.w t = southChart.w (-1 / t) * |1 / t ^ 2| := by
  rw [south_w, north_w]
  have : 1 + (-1 / t) ^ 2 = (1 + t ^ 2) / t ^ 2 := by field_simp; ring
  rw [this, abs_of_pos (by positivity)]; field_simp

end MarkovTriple.BGL.Instances.Riemannian.R26
