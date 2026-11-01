import Mathlib
import MarkovTriple.FunctionalInequalities.BEMain3

/-! # Bakry–Émery (Phase 4b): the second derivative `q' ≥ -2ρ q` -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

theorem exists_deriv_qFun [IsProbabilityMeasure F.μ] (hB : BEStable F) {ρ : ℝ}
    (hCD : F.CDFull ρ ∞) {φ : E → ℝ} (hφ : φ ∈ F.A₀) (h0 : 0 ≤ᵐ[F.μ] φ) {M : ℝ} (hM : 0 < M)
    (hb : ∀ᵐ x ∂F.μ, |φ x| ≤ M) {ε : ℝ} (hε : 0 < ε) (C : Cut ε M) {s : ℝ} (hs : 0 < s) :
    ∃ q' : ℝ, HasDerivAt (qFun F hφ C) q' s ∧ -2 * ρ * qFun F hφ C s ≤ q' := by
  obtain ⟨K, hK⟩ := exists_bounds C.hΘ C.hΘc
  obtain ⟨M₁, hM₁, hb₁⟩ := bound_L F hB hφ
  have hN2 := hasDerivAt_int_comp_mul (Λ := deriv C.Θ) (contDiff_deriv_top C.hΘ)
    (K₀ := K) (K₁ := K) (K₂ := K) (M := M₁)
    (fun x => (hK x).2.1) (fun x => (hK x).2.2.1) (fun x => (hK x).2.2.2) hM₁.le
    (a := aflow F hφ ε) (b := orb F (F.L_mem φ hφ))
    (a' := orb F (F.L_mem φ hφ) s) (b' := orb F (F.L_mem (F.L φ) (F.L_mem φ hφ)) s) (s := s)
    (hasDerivAt_aflow F hφ ε hs) (hasDerivAt_orb F (F.L_mem φ hφ) hs)
    (Filter.Eventually.of_forall fun r => orb_abs_le (F.L_mem φ hφ) hM₁ hb₁ r)
  refine ⟨_, hN2, ?_⟩
  obtain ⟨u, huA, hru, hLL, hflow, hV, hW⟩ := step F hB hφ h0 hM hb hε C hs
  have hrange := aflow_range hφ h0 hM hb ε s
  have hHA : (fun x => Real.exp (u x)) ∈ F.A := exp_comp_mem F huA
  have hHb := memLp_exp_top F huA hru.bdd
  have hLHb := memLp_LG_top F huA hru
  have hH2 := memLp_of_memLp_top hHb 2
  have hLH2 := memLp_of_memLp_top hLHb 2
  have hu2 := memLp_of_memLp_top hru.bdd 2
  have hLHA : F.L (fun x => Real.exp (u x)) ∈ F.A := F.L_mem_A _ hHA
  have hI := F.ibp_AA (fun x => Real.exp (u x)) hHA u huA hH2 hLH2 hu2
    (memLp_of_memLp_top hru.Lbdd 2) hru.bdd
  have eΓ := Γ_exp_comp F huA huA
  have hL0 : ∫ x, F.L (fun y => Real.exp (u y)) x ∂F.μ = 0 := integral_L_A F hHA hH2 hLH2
  have hLL0 : ∫ x, F.L (F.L (fun y => Real.exp (u y))) x ∂F.μ = 0 :=
    integral_L_A F hLHA hLH2 hLL
  have iuLH : Integrable (fun x => u x * F.L (fun y => Real.exp (u y)) x) F.μ :=
    integrable_top_mul_two hru.bdd hLH2
  have iLH : Integrable (fun x => F.L (fun y => Real.exp (u y)) x) F.μ :=
    hLH2.integrable one_le_two
  have iuLL : Integrable (fun x => u x * F.L (F.L (fun y => Real.exp (u y))) x) F.μ :=
    integrable_top_mul_two hru.bdd hLL
  have iLL : Integrable (fun x => F.L (F.L (fun y => Real.exp (u y))) x) F.μ :=
    hLL.integrable one_le_two
  -- the value of `q`
  have hq : qFun F hφ C s = -∫ x, Real.exp (u x) * F.Γ u u x ∂F.μ := by
    unfold qFun
    have e1 : ∀ᵐ x ∂F.μ, deriv C.Θ ((aflow F hφ ε s : Lp ℝ 2 F.μ) x) *
        (orb F (F.L_mem φ hφ) s : Lp ℝ 2 F.μ) x =
        u x * F.L (fun y => Real.exp (u y)) x + F.L (fun y => Real.exp (u y)) x := by
      filter_upwards [hflow, hV, hrange] with x h1 h2 h3
      rw [C.deriv_Θ_eq hε h3, h2, h1, Real.log_exp]; ring
    rw [integral_congr_ae e1, integral_add iuLH iLH, hL0, hI.2, eΓ]
    ring
  -- the value of `q'`
  have hD : (∫ x, deriv (deriv C.Θ) ((aflow F hφ ε s : Lp ℝ 2 F.μ) x) *
        ((orb F (F.L_mem φ hφ) s : Lp ℝ 2 F.μ) x * (orb F (F.L_mem φ hφ) s : Lp ℝ 2 F.μ) x) ∂F.μ) +
      ∫ x, deriv C.Θ ((aflow F hφ ε s : Lp ℝ 2 F.μ) x) *
        (orb F (F.L_mem (F.L φ) (F.L_mem φ hφ)) s : Lp ℝ 2 F.μ) x ∂F.μ =
      (∫ x, (F.L (fun y => Real.exp (u y)) x) ^ 2 / Real.exp (u x) ∂F.μ) +
        ∫ x, u x * F.L (F.L (fun y => Real.exp (u y))) x ∂F.μ := by
    have e2 : ∀ᵐ x ∂F.μ, deriv (deriv C.Θ) ((aflow F hφ ε s : Lp ℝ 2 F.μ) x) *
        ((orb F (F.L_mem φ hφ) s : Lp ℝ 2 F.μ) x * (orb F (F.L_mem φ hφ) s : Lp ℝ 2 F.μ) x) =
        (F.L (fun y => Real.exp (u y)) x) ^ 2 / Real.exp (u x) := by
      filter_upwards [hflow, hV, hrange] with x h1 h2 h3
      rw [C.deriv_deriv_Θ_eq hε h3, h2, h1, inv_mul_eq_div, sq]
    have e3 : ∀ᵐ x ∂F.μ, deriv C.Θ ((aflow F hφ ε s : Lp ℝ 2 F.μ) x) *
        (orb F (F.L_mem (F.L φ) (F.L_mem φ hφ)) s : Lp ℝ 2 F.μ) x =
        u x * F.L (F.L (fun y => Real.exp (u y))) x + F.L (F.L (fun y => Real.exp (u y))) x := by
      filter_upwards [hflow, hW, hrange] with x h1 h2 h3
      rw [C.deriv_Θ_eq hε h3, h2, h1, Real.log_exp]; ring
    rw [integral_congr_ae e2, integral_congr_ae e3, integral_add iuLL iLL, hLL0]
    ring
  rw [hD, hq]
  have := alg F hCD huA hru hLL
  linarith

end MarkovTriple.BE
