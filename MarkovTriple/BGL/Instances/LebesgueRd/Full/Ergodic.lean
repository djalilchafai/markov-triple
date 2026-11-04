import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Esa

/-!
# S10 (`ergodic_lebesgueRd`) for `(ℝ^d, Lebesgue)` (Round 24, stream A, part B-b)

`u ∈ 𝒟(L)`, `L u = 0` ⇒ `⟪u, L a⟫ = 0` for `a ∈ 𝒜₀` (symmetry of the generator); transported to
`heatL2 (Δφ) s` through the cut-off approximants (`heat_graph`); so `g(s) = ⟪u, heatL2 φ s⟫` has
`g' = s ⟪u, heatL2 (Δφ) s⟫ = 0`, is constant, and tends to `0` as `s → ∞`: `⟪u, φ⟫ = g(0) = 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL.LebesgueRd

open MarkovTriple.BGL

variable {d : ℕ}

theorem inner_heatL_eq_zero (hd : 1 ≤ d) {u : Lp ℝ 2 (volume : Measure (Fin d → ℝ))}
    (hu : u ∈ (lebesgueRdDiffusion d hd).generator.domain)
    (h : (lebesgueRdDiffusion d hd).generator ⟨u, hu⟩ = 0)
    {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (s : ℝ) : inner ℝ u (heatL2 (Lf φ) s) = 0 := by
  set T := lebesgueRdDiffusion d hd
  obtain ⟨a, c1, c2⟩ := heat_graph hd hφ s
  have hz : ∀ n, inner ℝ u (T.Lcls (a n)) = 0 := by
    intro n
    have hs := Hilbert.FormData.generator_symm (DiffusionTriple.formData T) hu
      (DiffusionTriple.cls_mem_generator_domain T (a n))
    have hGa := DiffusionTriple.generator_cls T (a n) (DiffusionTriple.cls_mem_generator_domain T (a n))
    change inner ℝ (T.generator ⟨u, hu⟩) (T.cls (a n)) =
      inner ℝ u (T.generator ⟨T.cls (a n), DiffusionTriple.cls_mem_generator_domain T (a n)⟩) at hs
    rw [hGa, h, inner_zero_left] at hs
    exact hs.symm
  have hlim : Tendsto (fun n => inner ℝ u (T.Lcls (a n))) atTop
      (𝓝 (inner ℝ u (heatL2 (Lf φ) s))) := tendsto_const_nhds.inner c2
  rw [show (fun n => inner ℝ u (T.Lcls (a n))) = fun _ => (0 : ℝ) from funext hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **S10** for `(ℝ^d, Lebesgue)`. -/
theorem ergodic_lebesgueRd (hd : 1 ≤ d) (u : Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    (hu : u ∈ (lebesgueRdDiffusion d hd).generator.domain)
    (h : (lebesgueRdDiffusion d hd).generator ⟨u, hu⟩ = 0) :
    ∃ c : ℝ, (u : (Fin d → ℝ) → ℝ) =ᵐ[volume] fun _ => c := by
  have hu0 : u = 0 := by
    refine (lebesgueRdDiffusion d hd).eq_zero_of_orth u (fun g => ?_)
    obtain ⟨φ, hφ⟩ := g
    set G : ℝ → ℝ := fun s => inner ℝ u (heatL2 φ s) with hG
    have hder : ∀ s, HasDerivAt G 0 s := fun s => by
      have := hasDerivAt_inner_heat hφ u s
      rwa [inner_heatL_eq_zero hd hu h hφ s, mul_zero] at this
    have hc : ∀ s, G s = G 0 := fun s =>
      is_const_of_deriv_eq_zero (fun x => (hder x).differentiableAt) (fun x => (hder x).deriv) s 0
    have hlim : Tendsto G atTop (𝓝 0) := by
      have : Tendsto G atTop (𝓝 (inner ℝ u (0 : Lp ℝ 2 (volume : Measure (Fin d → ℝ))))) :=
        tendsto_const_nhds.inner (tendsto_heatL2_zero hφ hd)
      simpa using this
    have h0 : G 0 = 0 := by
      refine tendsto_nhds_unique ?_ hlim
      exact tendsto_const_nhds.congr (fun s => (hc s).symm)
    simp only [hG] at h0
    rw [heatL2_zero hφ] at h0
    exact h0
  refine ⟨0, ?_⟩
  rw [hu0]
  exact Lp.coeFn_zero _ _ _

end MarkovTriple.BGL.LebesgueRd
