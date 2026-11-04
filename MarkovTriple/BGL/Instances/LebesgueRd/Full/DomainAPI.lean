import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAPI
import MarkovTriple.BGL.Instances.LebesgueRd.Gamma2
import MarkovTriple.BGL.Instances.Gibbs.FunctPreFull
import MarkovTriple.BGL.Frozen.Complete

/-!
# Completeness, `PreFull`, cut-off approximation and domain membership for `(ℝ^d, Lebesgue)` (Round 24, stream A, part B-a)

STUB (statements fixed; proofs `sorry` until stream B-a delivers).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

/-- completeness (BGL Def. 3.3.9) with cut-offs `ζ_k = s(2 - ψ/(M(k+1)))`, `ψ = √(1+|x|²)`. -/
theorem isComplete_lebesgueRd (hd : 1 ≤ d) : (lebesgueRdDiffusion d hd).IsComplete := sorry

/-- the semigroup-free extended-algebra axioms F1, F2, F4–F7, F9 for `𝒜 = C^∞` (assembly of `FullEasy.lean`). -/
theorem preFull_lebesgueRd (hd : 1 ≤ d) : PreFull (lebesgueRdDiffusion d hd) (A d) := sorry

/-- smooth `u` with `u, ∂ᵢu, Δu ∈ L²` lies in `𝒟(L)` with `L u = Δu` (cut-offs + closedness of the Friedrichs generator). -/
theorem domain_of_smooth_L2 (hd : 1 ≤ d) {u : (Fin d → ℝ) → ℝ} (hu : Sm u) (h0 : MemLp u 2 volume)
    (h1 : ∀ i, MemLp (dd i u) 2 volume) (h2 : MemLp (Lf u) 2 volume) :
    ∃ h : h0.toLp u ∈ (lebesgueRdDiffusion d hd).generator.domain,
      (lebesgueRdDiffusion d hd).generator ⟨h0.toLp u, h⟩ = h2.toLp (Lf u) := sorry

/-- limits of graph-convergent test functions lie in the domain (closedness of the generator). -/
theorem domain_of_approx (hd : 1 ≤ d) {u y : Lp ℝ 2 (volume : Measure (Fin d → ℝ))} (a : ℕ → (Fin d → ℝ) → ℝ)
    (ha : ∀ n, a n ∈ A₀ d)
    (h1 : Tendsto (fun n => (lebesgueRdDiffusion d hd).cls ⟨a n, ha n⟩) atTop (𝓝 u))
    (h2 : Tendsto (fun n => (lebesgueRdDiffusion d hd).Lcls ⟨a n, ha n⟩) atTop (𝓝 y)) :
    ∃ h : u ∈ (lebesgueRdDiffusion d hd).generator.domain,
      (lebesgueRdDiffusion d hd).generator ⟨u, h⟩ = y := sorry

/-- the smoothed test functions lie in `𝒟(L)`, `L (heat φ) = heat (Δφ)` (uses only the `HeatAPI` facts). -/
theorem heatL2_mem_domain (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) (a : ℝ) :
    ∃ h : heatL2 φ a ∈ (lebesgueRdDiffusion d hd).generator.domain,
      (lebesgueRdDiffusion d hd).generator ⟨heatL2 φ a, h⟩ = heatL2 (Lf φ) a := sorry

end MarkovTriple.BGL.LebesgueRd
