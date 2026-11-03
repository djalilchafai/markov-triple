import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllDiff
import MarkovTriple.BGL.Instances.Gibbs.FunctESA
import MarkovTriple.BGL.Instances.Gibbs.FunctPreFull
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Theory.Poincare
import MarkovTriple.BGL.Theory.LogSobolevMain
import MarkovTriple.BGL.Theory.GradientBound

/-!
# The weighted elliptic triple on `ℝ^d`: extended algebra `𝒜 = C^∞`, ESA, ergodicity, Poincaré, Full triple

Mirrors the one-dimensional development `Instances/Gibbs/Funct{Algebra,PI,Full}.lean` for `E : EllData d`.

Proved with no hypothesis beyond `EllData`: `preFull : PreFull E.diff (Afull d)` (F1, F2, F4–F7, F9 of BGL
Def. 3.3.1/3.3.7), the integrated identity (3.3.8) `integral_Γ₂`, and the integrated curvature inequality from the
pointwise one.

NAMED HYPOTHESES (never axioms, same as the 1-D case): `WeakHypo` (Def. 3.3.8, elliptic regularity of
`L f = λ f` weak solutions; quoted by the book, Sect. 1.12), `F8` (Def. 3.3.1 (viii), `P_t 𝒜₀ ⊂ 𝒜`),
and the curvature hypothesis `Curv ρ` (Def. 3.3.14, `n = ∞`, on smooth functions, stated for the formula-defined
`Γ₂`).  Under `WeakHypo`: ESA (F10, Prop. 3.3.11) and ergodicity (S10, Prop. 3.3.10); with `Curv ρ`, `ρ > 0`: the
Poincaré inequality with constant `1/ρ`; with `F8` additionally the Full triple `E.full`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple PreFull FullTriple StandardTriple)

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- positivity detection (F2) for smooth functions, via a bump function. -/
lemma pos_detect_aux {f : Rd d → ℝ} (hf : Sm f)
    (h : ∀ g ∈ A₀ d, 0 ≤ᵐ[E.μ] g → 0 ≤ ∫ x, g x * f x ∂E.μ) : ∀ x, 0 ≤ f x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0⟩ := hcon
  have hnhds : ∀ᶠ y in 𝓝 x0, f y < 0 := hf.continuous.continuousAt.eventually_lt
    continuousAt_const hx0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hnhds
  let b : ContDiffBump x0 := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hb_mem : (fun y => b y) ∈ A₀ d := ⟨b.contDiff, b.hasCompactSupport⟩
  have hnn : 0 ≤ᵐ[E.μ] fun y => b y := Eventually.of_forall fun y => b.nonneg
  have h1 := h _ hb_mem hnn
  have hle : ∀ y, 0 ≤ -(b y * f y) := by
    intro y
    by_cases hy : dist y x0 < r
    · have := hball hy
      have hby : 0 ≤ b y := b.nonneg
      have := mul_nonneg hby (neg_nonneg.2 this.le)
      linarith
    · have : b y = 0 := b.zero_of_le_dist (by simpa [b] using not_lt.1 hy)
      simp [this]
  have hcont : Continuous fun y => -(b y * f y) := (b.continuous.mul hf.continuous).neg
  have hcs : HasCompactSupport fun y => -(b y * f y) :=
    (b.hasCompactSupport.mul_right (f' := f)).neg
  have hne : (fun y => -(b y * f y)) x0 ≠ 0 := by
    have : b x0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp only [this, one_mul, neg_ne_zero]
    exact hx0.ne
  have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := E.μ) hcs hle hne
  rw [integral_neg] at hpos
  linarith

instance : IsProbabilityMeasure E.diff.μ := inferInstanceAs (IsProbabilityMeasure E.μ)

/-- **`PreFull`**: the semigroup-free axioms of the extended algebra `𝒜 = C^∞(ℝ^d)` (F1, F2, F4–F7, F9). -/
theorem preFull : PreFull E.diff (Afull d) where
  A₀_le := fun f hf => hf.1
  A_measurable := fun f hf => (show Sm f from hf).continuous.measurable
  ideal := fun f hf h hh => ⟨(hh.1).mul (show Sm f from hf), hh.2.mul_right⟩
  pos_detect := fun f hf h =>
    Eventually.of_forall (E.pos_detect_aux (show Sm f from hf) h)
  L_mem_A := fun f hf => E.sm_L (show Sm f from hf)
  ΓA_nonneg := fun f hf => Eventually.of_forall fun x => by
    have := congrFun (E.ΓA_eq (show Sm f from hf) (show Sm f from hf)) x
    show 0 ≤ E.diff.ΓA f f x
    rw [this]
    exact E.Γ_nonneg f x
  diffusion_Γ_A := fun k ψ hψ f hf g hg => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => hf i
    have hg' : Sm g := hg
    have key : ∀ i, E.diff.ΓA (f i) g = E.Γ (f i) g := fun i => E.ΓA_eq (hf' i) hg'
    show E.diff.ΓA (fun x => ψ (fun i => f i x)) g x = _
    rw [E.ΓA_eq (sm_comp k ψ hψ f hf') hg', E.Γ_comp ψ hψ f hf' g x]
    exact Finset.sum_congr rfl fun i _ => by
      show _ = _ * E.diff.ΓA (f i) g x
      rw [key i]
  ibp_A := fun f hf g hg => by
    have hf' : Sm f := hf
    have e : E.diff.ΓA f g = E.Γ f g := E.ΓA_eq hf' hg.1
    refine ⟨?_, ?_⟩
    · show ∫ x, E.diff.ΓA f g x ∂E.μ = -∫ x, g x * E.L f x ∂E.μ
      rw [e, E.ibp_sm hf' hg.1 (Or.inl hg.2), neg_neg, E.Γ_symm]
    · show ∫ x, E.diff.ΓA f g x ∂E.μ = -∫ x, f x * E.L g x ∂E.μ
      rw [e, E.ibp_sm hg.1 hf' (Or.inr hg.2)]
      simp
  connected := fun f hf h => by
    have hf' : Sm f := hf
    have h1 : E.diff.ΓA f f =ᵐ[E.μ] 0 := h
    rw [E.ΓA_eq hf' hf'] at h1
    have h3 : E.Γ f f = 0 :=
      (Continuous.ae_eq_iff_eq E.μ (E.sm_Γ hf' hf').continuous continuous_const).1 h1
    have h4 : ∀ x, fderiv ℝ f x = 0 := by
      intro x
      have hx : E.Γ f f x = 0 := congrFun h3 x
      have hv : (fun i => pderiv f i x) = 0 := by
        by_contra hne
        have := E.a_pos x _ hne
        have e2 : ∑ i, ∑ j, E.a i j x * (pderiv f i x) * (pderiv f j x) = E.Γ f f x := rfl
        linarith
      ext v
      rw [MarkovTriple.Sanity.OU.clm_pi_apply]
      simp only [zero_apply]
      exact Finset.sum_eq_zero fun i _ => by
        have := congrFun hv i
        simp only [pderiv] at this
        simp [this]
    have h5 := fun x y => is_const_of_fderiv_eq_zero (hf'.differentiable (by simp)) h4 (x := x) (y := y)
    exact ⟨f 0, Eventually.of_forall fun x => h5 x 0⟩

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
