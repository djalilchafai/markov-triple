import Mathlib
import MarkovTriple.BGL.Theory.ALevel
import MarkovTriple.BGL.Theory.Gamma2Integral
import MarkovTriple.BGL.Semigroup.Mass

/-!
# Gradient bound `Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)` (BGL Cor. 3.3.19, via the interpolation of Thm 3.3.18)

**Status: proved conditionally on an explicit regularity hypothesis, `GradientInterpolation T`.**

The book's argument (proof of Thm 3.3.18) studies, for `f, h ∈ 𝒜₀`, `h ≥ 0`, `t > 0`, the function
`Φ(s) = ∫ P_s h · Γ(P_{t-s} f) dμ` on `[0, t]`.  Formally `Φ'(s) = 2 ∫ P_s h · Γ₂(P_{t-s} f) dμ ≥
2ρ Φ(s)` by `CD(ρ, ∞)`, so `e^{-2ρ s} Φ(s)` is nondecreasing and `Φ(0) ≤ e^{-2ρ t} Φ(t)`.  The
justification of the differentiation of `Φ` (integrability of the integrands, differentiation under
the integral sign, symmetric integration by parts for `P_s h ∈ 𝒜 ∖ 𝒜₀`) is the content of
Lemmas 3.3.20–3.3.21 of the book (via `√(Γ(·) + ε²) - ε ∈ 𝒟(ℰ)`); it needs the extension of `Γ₂`
and of the Hessian to `𝒟(L)` (Props. 3.3.16–3.3.17), which is NOT available from F1–F10 in this
development.  We therefore isolate EXACTLY the output of that analysis as the structure
`GradientInterpolation T` (a `Prop`-valued hypothesis, never an axiom) and prove everything else:

* the real-variable Gronwall step (`gradient_integrated`),
* the identification of the end points (`P_0 = id`, `P_t` self-adjoint, `Γ` depends only on
  a.e.-classes), and
* the pointwise a.e. bound from the integrated one via positivity detection F2
  (`gradient_bound`).

See `Theory/GAPS.md`, item G1, for the exact missing lemma.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- `∫ P_t h · c = ∫ h · P_t c` for test functions (symmetry of `P_t`, with `𝒜`-representatives). -/
theorem integral_Pt_mul (t : ℝ≥0) (h c : T.A₀) :
    ∫ x, T.Pt t h x * c.1 x ∂T.μ = ∫ x, h.1 x * T.Pt t c x ∂T.μ := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (T.toDiffusionTriple.semigroup_isSelfAdjoint t) (T.toDiffusionTriple.cls h)
    (T.toDiffusionTriple.cls c)
  rw [L2_inner_eq, L2_inner_eq] at hs
  have e1 : ∫ x, T.Pt t h x * c.1 x ∂T.μ = ∫ x, ((T.toDiffusionTriple.semigroup t
      (T.toDiffusionTriple.cls h) : Lp ℝ 2 T.μ) : E → ℝ) x *
      ((T.toDiffusionTriple.cls c : Lp ℝ 2 T.μ) : E → ℝ) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_ae t h, DiffusionTriple.coeFn_cls T.toDiffusionTriple c] with x h1 h2
    rw [h1, h2]
  have e2 : ∫ x, h.1 x * T.Pt t c x ∂T.μ = ∫ x, ((T.toDiffusionTriple.cls h : Lp ℝ 2 T.μ) :
      E → ℝ) x * ((T.toDiffusionTriple.semigroup t (T.toDiffusionTriple.cls c) :
      Lp ℝ 2 T.μ) : E → ℝ) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_ae t c, DiffusionTriple.coeFn_cls T.toDiffusionTriple h] with x h1 h2
    rw [h1, h2]
  rw [e1, e2]; exact hs

/-- `s ↦ ∫ P_s h · Γ(P_{t-s} f) dμ`, the interpolation function of the book (proof of Thm 3.3.18).
Representatives of `P_s h`, `P_{t-s} f` in `𝒜` are chosen by `Pt`. -/
noncomputable def gradPhi (f h : T.A₀) (t : ℝ≥0) (s : ℝ) : ℝ :=
  ∫ x, T.Pt s.toNNReal h x *
    T.toDiffusionTriple.ΓA (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ

/-- **The regularity hypothesis for the semigroup interpolation (G1 of `GAPS.md`).**  For `f, h ∈ 𝒜₀`
with `h ≥ 0` and `t ≥ 0`, writing `k_s = P_s h`, `g_s = P_{t-s} f` (representatives in `𝒜`):

* `s ↦ Φ(s) = ∫ k_s Γ(g_s)` is continuous on `[0,t]`;
* for `0 < s < t`: `k_s Γ(g_s)` and `k_s Γ₂(g_s)` are integrable and `Φ'(s) = 2 ∫ k_s Γ₂(g_s)`.

This is exactly what Lemmas 3.3.20–3.3.21 of the book establish (there with the `ε`-regularisation);
it is true in the classical examples but NOT derived from F1–F10 here.  It is a hypothesis only. -/
structure GradientInterpolation : Prop where
  continuousOn : ∀ (f h : T.A₀), 0 ≤ᵐ[T.μ] h.1 → ∀ t : ℝ≥0,
    ContinuousOn (T.gradPhi f h t) (Icc 0 (t : ℝ))
  hasDerivAt : ∀ (f h : T.A₀), 0 ≤ᵐ[T.μ] h.1 → ∀ t : ℝ≥0, ∀ s ∈ Ioo (0 : ℝ) (t : ℝ),
    Integrable (fun x => T.Pt s.toNNReal h x *
      T.toDiffusionTriple.ΓA (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x)
      T.μ ∧
    Integrable (fun x => T.Pt s.toNNReal h x *
      T.toDiffusionTriple.Γ₂ (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x)
      T.μ ∧
    HasDerivAt (T.gradPhi f h t) (2 * ∫ x, T.Pt s.toNNReal h x *
      T.toDiffusionTriple.Γ₂ (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ)
      s

/-- **Integrated gradient bound** (real-variable step of the proof of Thm 3.3.18):
`Φ(0) ≤ e^{-2ρt} Φ(t)`. -/
theorem gradient_integrated {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hG : T.GradientInterpolation)
    (f h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) (t : ℝ≥0) :
    T.gradPhi f h t 0 ≤ Real.exp (-2 * ρ * t) * T.gradPhi f h t t := by
  set Φ := T.gradPhi f h t with hΦ
  set Ψ : ℝ → ℝ := fun s => Real.exp (-2 * ρ * s) * Φ s with hΨ
  have hexp : Continuous fun s : ℝ => Real.exp (-2 * ρ * s) := by fun_prop
  have hcont : ContinuousOn Ψ (Icc 0 (t : ℝ)) := hexp.continuousOn.mul (hG.continuousOn f h hh t)
  have hder : ∀ s ∈ Ioo (0 : ℝ) (t : ℝ), ∃ d, HasDerivAt Ψ d s ∧ 0 ≤ d := by
    intro s hs
    obtain ⟨i1, i2, hd⟩ := hG.hasDerivAt f h hh t s hs
    set g := T.Pt ((t : ℝ) - s).toNNReal f with hg
    set k := T.Pt s.toNNReal h with hk
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-2 * ρ * s))
        (Real.exp (-2 * ρ * s) * (-2 * ρ)) s := by
      have := ((hasDerivAt_id s).const_mul (-2 * ρ)).exp
      simpa using this
    refine ⟨_, h1.mul hd, ?_⟩
    have hk0 : 0 ≤ᵐ[T.μ] k := T.Pt_nonneg _ h hh
    have hcd := hCD.2 g (T.Pt_mem_A _ f)
    have hpos : 0 ≤ ∫ x, k x * (T.toDiffusionTriple.Γ₂ g g x -
        ρ * T.toDiffusionTriple.ΓA g g x) ∂T.μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hk0, hcd] with x h1 h2
      have : 0 ≤ (n⁻¹).toReal * (T.L g x) ^ 2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
      exact mul_nonneg h1 (by linarith)
    have e : ∫ x, k x * (T.toDiffusionTriple.Γ₂ g g x - ρ * T.toDiffusionTriple.ΓA g g x) ∂T.μ =
        ∫ x, k x * T.toDiffusionTriple.Γ₂ g g x ∂T.μ -
          ρ * ∫ x, k x * T.toDiffusionTriple.ΓA g g x ∂T.μ := by
      have : (fun x => k x * (T.toDiffusionTriple.Γ₂ g g x - ρ * T.toDiffusionTriple.ΓA g g x)) =
          fun x => k x * T.toDiffusionTriple.Γ₂ g g x -
            ρ * (k x * T.toDiffusionTriple.ΓA g g x) := by
        funext x; ring
      rw [this, integral_sub i2 (i1.const_mul ρ), integral_const_mul]
    have hΦs : Φ s = ∫ x, k x * T.toDiffusionTriple.ΓA g g x ∂T.μ := rfl
    have hpe := Real.exp_pos (-2 * ρ * s)
    have : 0 ≤ Real.exp (-2 * ρ * s) * (-2 * ρ) * Φ s +
        Real.exp (-2 * ρ * s) * (2 * ∫ x, k x * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) := by
      rw [hΦs]
      have := mul_nonneg hpe.le (by linarith : 0 ≤ 2 * (∫ x, k x * T.toDiffusionTriple.Γ₂ g g x ∂T.μ -
          ρ * ∫ x, k x * T.toDiffusionTriple.ΓA g g x ∂T.μ))
      nlinarith [this]
    simpa [hΨ, mul_comm, mul_left_comm, mul_assoc] using this
  have hmono : MonotoneOn Ψ (Icc 0 (t : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (let ⟨_, hd, _⟩ := hder s hs; hd.differentiableAt.differentiableWithinAt)
    · rw [interior_Icc]
      intro s hs
      obtain ⟨d, hd, hle⟩ := hder s hs
      rw [hd.deriv]; exact hle
  have := hmono (a := 0) (b := (t : ℝ)) (by simp) (by simp) t.2
  simpa [hΨ] using this

/-- **Gradient bound** (BGL Cor. 3.3.19), conditional on `GradientInterpolation`:
for `f ∈ 𝒜₀`, `t ≥ 0`, `Γ(P_t f) ≤ e^{-2ρt} P_t(Γ f)` a.e. (any `n`: `CD(ρ,n)`).  `P_t(Γ f)` is
the class `semigroup t [Γ f]`, `Γ f ∈ 𝒜₀`. -/
theorem gradient_bound {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hG : T.GradientInterpolation)
    (f : T.A₀) (t : ℝ≥0) :
    T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) ≤ᵐ[T.μ] fun x =>
      Real.exp (-2 * ρ * t) * (T.toDiffusionTriple.semigroup t (T.toDiffusionTriple.cls
        ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 T.μ) x := by
  set c : T.A₀ := ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩ with hc
  set w := T.Pt t c with hw
  set Γt := T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) with hΓt
  have hwA : w ∈ T.A := T.Pt_mem_A t c
  have hΓA : Γt ∈ T.A := ΓA_mem_A T (T.Pt_mem_A t f) (T.Pt_mem_A t f)
  set u : E → ℝ := Real.exp (-2 * ρ * t) • w - Γt with hu
  have huA : u ∈ T.A := T.A.sub_mem (T.A.smul_mem hwA _) hΓA
  have hpos : 0 ≤ᵐ[T.μ] u := by
    refine T.pos_detect u huA (fun h hh h0 => ?_)
    set h' : T.A₀ := ⟨h, hh⟩
    have key := gradient_integrated T hCD hG f h' h0 t
    have eΦ0 : T.gradPhi f h' t 0 = ∫ x, h x * Γt x ∂T.μ := by
      unfold gradPhi
      refine integral_congr_ae ?_
      filter_upwards [T.Pt_zero h'] with x hx
      simp only [Real.toNNReal_zero, sub_zero, Real.toNNReal_coe, hΓt, hx]
      rfl
    have eΦt : T.gradPhi f h' t t = ∫ x, h x * w x ∂T.μ := by
      unfold gradPhi
      have hf0 := T.Pt_zero f
      have hcg : ∀ᵐ x ∂T.μ, T.toDiffusionTriple.ΓA (T.Pt (((t : ℝ) - t).toNNReal) f)
          (T.Pt (((t : ℝ) - t).toNNReal) f) x = c.1 x := by
        have := T.ΓA_congr_A (T.Pt_mem_A 0 f) (T.A₀_le f.1 f.2) (T.Pt_zero f)
        simp only [sub_self, Real.toNNReal_zero]
        exact this
      have : ∫ x, T.Pt (t : ℝ).toNNReal h' x * T.toDiffusionTriple.ΓA
          (T.Pt (((t : ℝ) - t).toNNReal) f) (T.Pt (((t : ℝ) - t).toNNReal) f) x ∂T.μ =
          ∫ x, T.Pt t h' x * c.1 x ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hcg] with x hx
        simp only [Real.toNNReal_coe, hx]
      rw [this, integral_Pt_mul T t h' c]
    rw [eΦ0, eΦt] at key
    have i1 : Integrable (fun x => h x * w x) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal w hwA h hh)
    have i2 : Integrable (fun x => h x * Γt x) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal Γt hΓA h hh)
    have e : (fun x => h x * u x) = fun x => Real.exp (-2 * ρ * t) * (h x * w x) - h x * Γt x := by
      funext x; simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, integral_sub (i1.const_mul _) i2, integral_const_mul]
    linarith
  filter_upwards [hpos, T.Pt_ae t c] with x hx hx2
  simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
  rw [hx2]; linarith

end FullTriple

end MarkovTriple.BGL
