import Mathlib
import MarkovTriple.BGL.Theory.Interp.Jensen
import MarkovTriple.BGL.Theory.Interp.Main
import MarkovTriple.BGL.Theory.Conservation.Mass

/-!
# Weak gradient bound (BGL Cor. 3.3.19) for every `FullTriple` with `CD(ρ,n)`, `ρ ≥ 0`

Cor 3.3.19 is deduced in the book (p. 163) from Thm 3.3.18 "by Jensen's inequality for `P_t`, which is
sub-Markov": `Γ(P_t f) ≤ e^{-2ρt} (P_t √Γ f)² ≤ e^{-2ρt} P_t Γ f`.  Here: `strong_gradient_bound_unconditional`
(`Interp/Main.lean`) + `jensen_sq` (`Interp/Jensen.lean`, applied to `P_t` which is positive and
sub-Markov by `semigroup_nonneg`, `semigroup_le_one`).  The conclusion is literally that of the conditional
`FullTriple.gradient_bound` (`GradientBound.lean`), and `HasGradientBound` (`Conservation/Estimate.lean`)
follows exactly as in `FullTriple.hasGradientBound`.  No `GradientInterpolation` hypothesis.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

namespace FullTriple

variable {E : Type*} [MeasurableSpace E] (T : FullTriple E)

/-- **Cor 3.3.19, unconditional** (`ρ ≥ 0`): `Γ(P_t f) ≤ e^{-2ρt} P_t(Γ f)` a.e. -/
theorem gradient_bound_unconditional {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ)
    (f : T.A₀) (t : ℝ≥0) :
    T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) ≤ᵐ[T.μ] fun x =>
      Real.exp (-2 * ρ * t) * (T.toDiffusionTriple.semigroup t (T.toDiffusionTriple.cls
        ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 T.μ) x := by
  have hs := T.strong_gradient_bound_unconditional hCD hρ f t
  have hf0 := T.ΓA_nonneg f.1 (T.A₀_le f.1 f.2)
  have hw : 0 ≤ᵐ[T.μ] (T.sqrtΓcls f : E → ℝ) := by
    filter_upwards [T.coeFn_sqrtΓcls f] with x hx
    rw [hx]; exact Real.sqrt_nonneg _
  have hW : (T.toDiffusionTriple.cls ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩ :
      E → ℝ) =ᵐ[T.μ] fun x => ((T.sqrtΓcls f : E → ℝ) x) ^ 2 := by
    filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple
      ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩, T.coeFn_sqrtΓcls f, hf0] with x a b c
    rw [a, b, Real.sq_sqrt c]
  have hJ := jensen_sq (T.toDiffusionTriple.semigroup t)
    (fun u hu => T.toDiffusionTriple.semigroup_nonneg t hu)
    (fun u hu => T.toDiffusionTriple.semigroup_le_one t u hu) (T.sqrtΓcls f) _ hw hW
  have hΓ0 := T.ΓA_nonneg _ (T.Pt_mem_A t f)
  filter_upwards [hs, hJ, hΓ0] with x h1 h2 h3
  simp only [Pi.zero_apply] at h3
  have e2 : Real.exp (-2 * ρ * t) = Real.exp (-ρ * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have h4 : T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) x ≤
      (Real.exp (-ρ * t) * (T.toDiffusionTriple.semigroup t (T.sqrtΓcls f) : Lp ℝ 2 T.μ) x) ^ 2 := by
    calc _ = (Real.sqrt (T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) x)) ^ 2 :=
          (Real.sq_sqrt h3).symm
      _ ≤ _ := by gcongr
  calc _ ≤ _ := h4
    _ = Real.exp (-2 * ρ * t) * ((T.toDiffusionTriple.semigroup t (T.sqrtΓcls f) : Lp ℝ 2 T.μ) x) ^ 2 := by
        rw [e2]; ring
    _ ≤ _ := by
        have := Real.exp_pos (-2 * ρ * t)
        exact mul_le_mul_of_nonneg_left h2 this.le

/-- **`HasGradientBound` discharged for every `FullTriple`** with `CD(ρ,n)`, `ρ ≥ 0`
(unconditional analogue of `FullTriple.hasGradientBound`). -/
theorem hasGradientBound_unconditional {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ) :
    HasGradientBound T.toDiffusionTriple T.A ρ := by
  intro f c hc t g hg hPg
  have h1 := T.gradient_bound_unconditional hCD hρ f t
  have e1 : T.toDiffusionTriple.ΓA g g =ᵐ[T.μ] T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) :=
    T.ΓA_congr_A hg (T.Pt_mem_A t f) (hPg.symm.trans (T.Pt_ae t f))
  have e2 : T.toDiffusionTriple.cls c = T.toDiffusionTriple.cls
      ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩ := by
    refine Lp.ext ?_
    filter_upwards [T.toDiffusionTriple.coeFn_cls c, hc,
      T.toDiffusionTriple.ΓA_ae_eq f.2 f.2, T.toDiffusionTriple.coeFn_cls
        ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩] with x a b d e
    rw [a, e]; exact b.trans d.symm
  rw [e2]
  filter_upwards [e1, h1] with x a b
  exact a.le.trans b

/-- **Mass conservation (BGL Thm 3.3.23, first claim) for every complete `FullTriple` with
`CD(ρ,n)`, `ρ ≥ 0`**, without `GradientInterpolation`. -/
theorem conservative_of_complete_unconditional {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ)
    (hC : T.toDiffusionTriple.IsComplete) {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, Tendsto (fun m => (T.toDiffusionTriple.exhP hu t m : E → ℝ) x) atTop (𝓝 1) :=
  T.extendedAlgebra.conservative_of_complete (T.hasGradientBound_unconditional hCD hρ) hC hu t

end FullTriple

end MarkovTriple.BGL
