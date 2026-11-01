import Mathlib
import MarkovTriple.FunctionalInequalities.BEMain2
import MarkovTriple.FunctionalInequalities.BENem2
import MarkovTriple.FunctionalInequalities.TripleSquare

/-! # Bakry–Émery (Phase 4b): `e' = q`, `q' ≥ -2ρ q` along the flow -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

lemma integral_L_A [IsFiniteMeasure F.μ] {f : E → ℝ} (hfA : f ∈ F.A) (hf : MemLp f 2 F.μ)
    (hLf : MemLp (F.L f) 2 F.μ) : ∫ x, F.L f x ∂F.μ = 0 := by
  have h1 : MemLp (1 : E → ℝ) 2 F.μ := memLp_const 1
  have hL : MemLp (F.L (1 : E → ℝ)) 2 F.μ := by rw [F.L_one]; exact MemLp.zero
  have hinf : MemLp (1 : E → ℝ) ∞ F.μ := memLp_const 1
  have := F.ibp_AA f hfA 1 F.A.one_mem hf hLf h1 hL hinf
  have e : F.Γ f (1 : E → ℝ) = 0 := by
    rw [F.Γ_symm_A f hfA 1 F.A.one_mem, F.Γ_one_left hfA]
  have h2 := this.2
  rw [e] at h2
  simpa using h2

/-- `e(r) = ∫ Θ(a_r)` -/
noncomputable def eFun [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) {ε M : ℝ} (C : Cut ε M)
    (r : ℝ) : ℝ := ∫ x, C.Θ ((aflow F hφ ε r : Lp ℝ 2 F.μ) x) ∂F.μ

/-- `q(r) = ∫ Θ'(a_r) b_r` with `b_r = P_r Lφ` -/
noncomputable def qFun [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) {ε M : ℝ} (C : Cut ε M)
    (r : ℝ) : ℝ :=
  ∫ x, deriv C.Θ ((aflow F hφ ε r : Lp ℝ 2 F.μ) x) * (orb F (F.L_mem φ hφ) r : Lp ℝ 2 F.μ) x ∂F.μ

theorem bound_L [IsFiniteMeasure F.μ] (hB : BEStable F) {φ : E → ℝ} (hφ : φ ∈ F.A₀) :
    ∃ M₁ : ℝ, 0 < M₁ ∧ ∀ᵐ x ∂F.μ, |F.L φ x| ≤ M₁ := by
  obtain ⟨C, hC⟩ := bd_of_memLp_top (hB.A₀_bdd (F.L φ) (F.L_mem φ hφ))
  exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    hC.mono fun x hx => hx.trans (le_max_left _ _)⟩

theorem hasDerivAt_eFun [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) {ε M : ℝ} (C : Cut ε M)
    {s : ℝ} (hs : 0 < s) : HasDerivAt (eFun F hφ C) (qFun F hφ C s) s := by
  obtain ⟨K, hK⟩ := exists_bounds C.hΘ C.hΘc
  exact hasDerivAt_int_comp C.hΘ (fun x => (hK x).1) (fun x => (hK x).2.1)
    (fun x => (hK x).2.2.1) (hasDerivAt_aflow F hφ ε hs)

end MarkovTriple.BE
