import Mathlib
import MarkovTriple.FunctionalInequalities.BEMain6
import MarkovTriple.FunctionalInequalities.BEGronwall
import MarkovTriple.Frozen.Ent
import MarkovTriple.Frozen.Fisher

/-! # Bakry–Émery (Phase 4b): the entropy–Fisher inequality `Ent(ε + φ) ≤ I(φ; ε)/(2ρ)` -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

/-- **Entropy–Fisher inequality** (the interpolation `Ent(h) ≤ (1/2ρ) ∫ Γ(h)/h`), for
`h = ε + φ`, `φ ∈ 𝒜₀`, `φ ≥ 0`, `ε > 0`.  Hypotheses: probability measure, `CD(ρ,∞)` on `𝒜`
(`CDFull`), `ρ > 0`, `ErgodicL2`, and the regularity hypothesis `BEStable`. -/
theorem ent_le_fisher [IsProbabilityMeasure F.μ] (hB : BEStable F) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : F.CDFull ρ ∞) (herg : F.toMarkovTriple.ErgodicL2) {φ : E → ℝ} (hφ : φ ∈ F.A₀)
    (h0 : 0 ≤ᵐ[F.μ] φ) {ε : ℝ} (hε : 0 < ε) :
    MarkovTriple.Ent F.μ (fun x => ε + φ x) ≤
      (∫ x, F.Γ φ φ x / (ε + φ x) ∂F.μ) / (2 * ρ) := by
  obtain ⟨C0, hC0⟩ := bd_of_memLp_top (hB.A₀_bdd φ hφ)
  set M : ℝ := max C0 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb : ∀ᵐ x ∂F.μ, |φ x| ≤ M := hC0.mono fun x hx => hx.trans (le_max_left _ _)
  obtain ⟨C⟩ := exists_cut hε hM.le
  set c : ℝ := ∫ x, φ x ∂F.μ with hc
  set m : ℝ := ε + c with hm
  have hφi : Integrable φ F.μ := integrable_of_mem F.toMarkovTriple hφ
  have hc0 : 0 ≤ c := integral_nonneg_of_ae h0
  have hcM : c ≤ M := by
    have : ∫ x, φ x ∂F.μ ≤ ∫ _x, M ∂F.μ :=
      integral_mono_ae hφi (integrable_const M)
        (hb.mono fun x hx => (le_abs_self _).trans hx)
    simpa using this
  have hmI : m ∈ Set.Icc ε (ε + M) := ⟨by linarith, by linarith⟩
  have key := ent_le_of_decay (e := fun r => eFun F hφ C r - C.Θ m) (q := qFun F hφ C) hρ
    ((continuous_eFun F hφ C).sub continuous_const).continuousOn
    (continuous_qFun F hφ C).continuousOn
    (fun s hs => (hasDerivAt_eFun F hφ C hs).sub_const _)
    (fun s hs => exists_deriv_qFun F hB hCD hφ h0 hM hb hε C hs)
    (tendsto_eFun F hρ hCD herg hφ C)
  rw [qFun_zero F hφ h0 hM hb hε C, neg_neg] at key
  have hrange := aflow_range hφ h0 hM hb ε 0
  have hint : (∫ x, (ε + φ x) ∂F.μ) = m := by
    rw [integral_add (integrable_const ε) hφi]; simp [hm, hc]
  have e0 : eFun F hφ C 0 = ∫ x, (ε + φ x) * Real.log (ε + φ x) ∂F.μ := by
    unfold eFun
    refine integral_congr_ae ?_
    filter_upwards [aflow_coe hφ ε 0, coeFn_cl F hφ, hrange] with x h1 h2 h3
    have h4 : (aflow F hφ ε 0 : E → ℝ) x = ε + φ x := by
      rw [h1, orb_zero, h2, add_comm]
    rw [h4] at h3 ⊢
    exact C.Θ_eq h3
  have hΘm : C.Θ m = m * Real.log m := C.Θ_eq hmI
  have hEnt : MarkovTriple.Ent F.μ (fun x => ε + φ x) = eFun F hφ C 0 - C.Θ m := by
    unfold MarkovTriple.Ent
    rw [e0, hΘm, hint]
  rw [hEnt]
  simpa using key

end MarkovTriple.BE
