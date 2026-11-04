import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.DirectExample

/-!
# Non-`𝒜₀` functions for the spiky potential: `f ≡ 1` and `f(x) = sin x₀` (R22, Stream E1, C2)

`spikyData d` (R20 `DirectExample`: `V = Σ v(xᵢ)`, `v'' = 2 + sin(e^{t²})`, `Hess V ≥ I`, not `GrowHess3`) was only exercised through the
generic theorem `spikyData_mem_domain_of_Γ₂`; here the hypotheses of `gibbsRd_mem_domain_of_Γ₂_direct` are verified for two functions
outside `𝒜₀ = C_c^∞`: the constant `1`, and the bounded non-constant, non-compactly supported `sin x₀`.  See `STATEMENTS_R22_E1.md`.

## DIFFERENCE FROM BGL
Both functions are bounded with bounded derivatives, hence trivially in `L²(μ)` with `Γ, Γ₂ ∈ L¹(μ)` (`μ` a probability measure); the
point is that the direct converse needs neither compact support nor any growth of `V`'s derivatives (here `∂³V` is unbounded and
super-polynomial) for such `f`.
-/

open MeasureTheory
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv FullTriple)
open MarkovTriple.BGL.Instances.Gibbs (spk spk_ge spk_le)

variable {d : ℕ}

/-- hypotheses in formula form (`Gr f f ∈ L¹`, Bochner expression of `Γ₂ ∈ L¹`) for the spiky potential. -/
theorem spikyData_mem_domain_of_formulas (d : ℕ) {f : Rd d → ℝ} (hfS : Sm f)
    (hf2 : MemLp f 2 (spikyData d).toEll.μ) (hG : Integrable (Gr f f) (spikyData d).toEll.μ)
    (hG2 : Integrable (fun x => ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 +
      ∑ i, ∑ j, pderiv (pderiv (spkVd d) i) j x * pderiv f i x * pderiv f j x) (spikyData d).toEll.μ) :
    ∃ hF : hf2.toLp f ∈ (spikyData d).gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      (((spikyData d).gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 (spikyData d).toEll.μ) : Rd d → ℝ) =ᵐ[(spikyData d).toEll.μ]
        (spikyData d).gibbsRdFull_unconditional.L f := by
  refine spikyData_mem_domain_of_Γ₂ d hfS hf2 ?_ ?_
  · have hGr : FullTriple.G (spikyData d).gibbsRdFull_unconditional f f = Gr f f := by
      show (spikyData d).toEll.diff.ΓA f f = Gr f f
      rw [(spikyData d).toEll.ΓA_eq hfS hfS, (spikyData d).toEll_Γ]
    rw [hGr]; exact hG
  · exact hG2.congr (Filter.Eventually.of_forall fun x => ((spikyData d).gibbsRd_Γ₂_eq hfS x).symm)

/-- **C2 (constant)**: `f ≡ 1 ∉ 𝒜₀` for the spiky potential. -/
theorem spikyData_const_mem_domain (d : ℕ) :
    ∃ hf2 : MemLp (fun _ : Rd d => (1 : ℝ)) 2 (spikyData d).toEll.μ,
      ∃ hF : hf2.toLp _ ∈ (spikyData d).gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      (((spikyData d).gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp _, hF⟩ :
        Lp ℝ 2 (spikyData d).toEll.μ) : Rd d → ℝ) =ᵐ[(spikyData d).toEll.μ]
        (spikyData d).gibbsRdFull_unconditional.L (fun _ => (1 : ℝ)) := by
  have hf2 : MemLp (fun _ : Rd d => (1 : ℝ)) 2 (spikyData d).toEll.μ := memLp_const 1
  refine ⟨hf2, spikyData_mem_domain_of_formulas d (contDiff_const) hf2 ?_ ?_⟩
  · have e : Gr (fun _ : Rd d => (1 : ℝ)) (fun _ => 1) = fun _ => 0 :=
      funext fun x => by simp [Gr, pderiv_const]
    rw [e]; exact integrable_zero _ _ _
  · have e : ∀ i : Fin d, pderiv (fun _ : Rd d => (1 : ℝ)) i = fun _ => 0 :=
      fun i => funext fun x => pderiv_const 1 i x
    simp [e, pderiv_const]

/-! ### `f(x) = sin x₀` -/

/-- `f(x) = sin(x₀)` on `ℝ^{d+1}`. -/
noncomputable def sinF (d : ℕ) : Rd (d + 1) → ℝ := fun x => Real.sin (x 0)

lemma sm_sinF (d : ℕ) : Sm (sinF d) := sm_fun_coord Real.sin Real.contDiff_sin 0

lemma pderiv_sinF (j : Fin (d + 1)) (x : Rd (d + 1)) :
    pderiv (sinF d) j x = if j = 0 then Real.cos (x 0) else 0 := by
  have := pderiv_fun_coord (d := d + 1) Real.sin Real.differentiable_sin 0 j x
  rw [Real.deriv_sin] at this
  exact this

lemma pderiv2_sinF (i j : Fin (d + 1)) (x : Rd (d + 1)) :
    pderiv (pderiv (sinF d) i) j x = if i = 0 then (if j = 0 then -Real.sin (x 0) else 0) else 0 := by
  have e : pderiv (sinF d) i = fun y => if i = 0 then Real.cos (y 0) else 0 :=
    funext fun y => pderiv_sinF i y
  rw [e]
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    have := pderiv_fun_coord (d := d + 1) Real.cos Real.differentiable_cos 0 j x
    rw [Real.deriv_cos'] at this
    exact this
  · simp only [hi, ite_false]
    exact pderiv_const 0 j x

lemma Gr_sinF (x : Rd (d + 1)) : Gr (sinF d) (sinF d) x = Real.cos (x 0) ^ 2 := by
  simp [Gr, pderiv_sinF, ite_mul, mul_ite, sq]

lemma Γ₂form_sinF (x : Rd (d + 1)) :
    ∑ i, ∑ j, pderiv (pderiv (sinF d) i) j x ^ 2 +
      ∑ i, ∑ j, pderiv (pderiv (spkVd (d + 1)) i) j x * pderiv (sinF d) i x * pderiv (sinF d) j x =
    Real.sin (x 0) ^ 2 + spk (x 0) * Real.cos (x 0) ^ 2 := by
  simp [pderiv2_sinF, pderiv2_spkVd, pderiv_sinF, ite_mul, mul_ite, sq]
  ring

/-- **C2 (sin)**: `f(x) = sin x₀ ∉ 𝒜₀` for the spiky potential on `ℝ^{d+1}` (`Γ f = cos² x₀`, `Γ₂ f = sin² x₀ + spk(x₀) cos² x₀`). -/
theorem spikyData_sin_mem_domain (d : ℕ) :
    ∃ hf2 : MemLp (sinF d) 2 (spikyData (d + 1)).toEll.μ,
      ∃ hF : hf2.toLp _ ∈ (spikyData (d + 1)).gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      (((spikyData (d + 1)).gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp _, hF⟩ :
        Lp ℝ 2 (spikyData (d + 1)).toEll.μ) : Rd (d + 1) → ℝ) =ᵐ[(spikyData (d + 1)).toEll.μ]
        (spikyData (d + 1)).gibbsRdFull_unconditional.L (sinF d) := by
  have hf2 : MemLp (sinF d) 2 (spikyData (d + 1)).toEll.μ :=
    MemLp.of_bound (sm_sinF d).continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  refine ⟨hf2, spikyData_mem_domain_of_formulas (d + 1) (sm_sinF d) hf2 ?_ ?_⟩
  · have e : Gr (sinF d) (sinF d) = fun x => Real.cos (x 0) ^ 2 := funext Gr_sinF
    rw [e]
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((Real.continuous_cos.comp (continuous_apply 0)).pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact Real.cos_sq_le_one _
  · have e : (fun x : Rd (d + 1) => ∑ i, ∑ j, pderiv (pderiv (sinF d) i) j x ^ 2 +
        ∑ i, ∑ j, pderiv (pderiv (spkVd (d + 1)) i) j x * pderiv (sinF d) i x * pderiv (sinF d) j x) =
        fun x => Real.sin (x 0) ^ 2 + spk (x 0) * Real.cos (x 0) ^ 2 := funext Γ₂form_sinF
    rw [e]
    refine Integrable.of_bound (C := 4) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have hc : Continuous fun x : Rd (d + 1) => spk (x 0) :=
        MarkovTriple.BGL.Instances.Gibbs.sm_spk.continuous.comp (continuous_apply 0)
      exact (((Real.continuous_sin.comp (continuous_apply 0)).pow 2).add
        (hc.mul ((Real.continuous_cos.comp (continuous_apply 0)).pow 2))).aestronglyMeasurable
    · have h1 := spk_ge (x 0)
      have h2 := spk_le (x 0)
      have h3 := Real.sin_sq_le_one (x 0)
      have h4 := Real.cos_sq_le_one (x 0)
      have h5 : 0 ≤ Real.cos (x 0) ^ 2 := sq_nonneg _
      have h6 : 0 ≤ Real.sin (x 0) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
      nlinarith

end MarkovTriple.BGL.Instances.GibbsRd
