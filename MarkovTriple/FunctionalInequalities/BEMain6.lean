import Mathlib
import MarkovTriple.FunctionalInequalities.BEMain5
import MarkovTriple.FunctionalInequalities.Poincare
import MarkovTriple.FunctionalInequalities.FormDomain

/-! # Bakry–Émery (Phase 4b): `e(T) → 0` as `T → ∞` (Poincaré ⟹ exponential decay) -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

lemma semigroup_one [IsFiniteMeasure F.μ] (t : ℝ≥0) :
    tripleSemigroup F.toMarkovTriple t (oneL2 F.μ) = oneL2 F.μ := by
  obtain ⟨-, -, -, -, -, -, hone, -⟩ := isSemigroupOf_full F
  refine Lp.ext ?_
  have h0 : ((oneL2 F.μ : Lp ℝ 2 F.μ) : E → ℝ) =ᵐ[F.μ] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  exact (hone t (oneL2 F.μ) h0).trans h0.symm

lemma coeFn_oneL2 [IsFiniteMeasure F.μ] :
    ((oneL2 F.μ : Lp ℝ 2 F.μ) : E → ℝ) =ᵐ[F.μ] fun _ => (1 : ℝ) :=
  MemLp.coeFn_toLp (memLp_const (1 : ℝ))

theorem tendsto_eFun [IsProbabilityMeasure F.μ] {ρ : ℝ} (hρ : 0 < ρ) (hCD : F.CDFull ρ ∞)
    (herg : F.toMarkovTriple.ErgodicL2) {φ : E → ℝ} (hφ : φ ∈ F.A₀) {ε M : ℝ} (C : Cut ε M) :
    Tendsto (fun T : ℝ => eFun F hφ C T - C.Θ (ε + ∫ x, φ x ∂F.μ)) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_bounds C.hΘ C.hΘc
  set c : ℝ := ∫ x, φ x ∂F.μ with hc
  set m : ℝ := ε + c with hm
  have hP := poincare_of_CD_infty F hρ hCD.toCD herg
  set w : Lp ℝ 2 F.μ := cl F hφ - c • oneL2 F.μ with hw
  have hcl : ∫ x, (cl F hφ : E → ℝ) x ∂F.μ = c := by
    rw [hc]; exact integral_congr_ae (coeFn_cl F hφ)
  have hw0 : inner ℝ w (oneL2 F.μ) = 0 := by
    have h1 : ∫ x, ((oneL2 F.μ : Lp ℝ 2 F.μ) : E → ℝ) x ∂F.μ = 1 := by
      rw [integral_congr_ae (coeFn_oneL2 F)]; simp
    rw [hw, inner_sub_left, inner_smul_left, inner_oneL2, inner_oneL2, hcl, h1]
    simp
  have hdec : ∀ T : ℝ≥0, ‖tripleSemigroup F.toMarkovTriple T w‖ ≤ Real.exp (-ρ * T) * ‖w‖ := by
    intro T
    have := expDecay_of_poincare F (one_div_pos.2 hρ) hP herg w hw0 T
    simpa [one_div] using this
  have hbound : ∀ r : ℝ, 0 ≤ r → ‖aflow F hφ ε r - m • oneL2 F.μ‖ ≤ Real.exp (-ρ * r) * ‖w‖ := by
    intro r hr
    have e1 : aflow F hφ ε r - m • oneL2 F.μ = tripleSemigroup F.toMarkovTriple r.toNNReal w := by
      rw [hw, map_sub, map_smul, semigroup_one, aflow, orb, hm, add_smul]
      abel
    rw [e1]
    have := hdec r.toNNReal
    rwa [Real.coe_toNNReal r hr] at this
  have hlim0 : Tendsto (fun r : ℝ => ‖aflow F hφ ε r - m • oneL2 F.μ‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun r => norm_nonneg _)
      ((eventually_ge_atTop (0 : ℝ)).mono fun r hr => hbound r hr) ?_
    have h1 : Tendsto (fun r : ℝ => Real.exp (-ρ * r)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using h1.mul_const ‖w‖
  have hconst : ∫ x, C.Θ ((m • oneL2 F.μ : Lp ℝ 2 F.μ) x) ∂F.μ = C.Θ m := by
    have : ∀ᵐ x ∂F.μ, C.Θ ((m • oneL2 F.μ : Lp ℝ 2 F.μ) x) = C.Θ m := by
      filter_upwards [Lp.coeFn_smul m (oneL2 F.μ), coeFn_oneL2 F] with x h1 h2
      rw [h1]; simp [h2]
    rw [integral_congr_ae this]; simp
  have hb2 : ∀ r : ℝ, |eFun F hφ C r - C.Θ m| ≤ K * (‖aflow F hφ ε r - m • oneL2 F.μ‖ *
      ‖oneL2 F.μ‖) := by
    intro r
    have := abs_int_comp_sub_le C.hΘ (fun x => (hK x).1) (fun x => (hK x).2.1)
      (aflow F hφ ε r) (m • oneL2 F.μ)
    rwa [hconst] at this
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun r => abs_nonneg _) hb2 ?_
  simpa using (hlim0.mul_const ‖oneL2 F.μ‖).const_mul K

end MarkovTriple.BE
