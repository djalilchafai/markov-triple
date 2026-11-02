import Mathlib
import MarkovTriple.BGL.Theory.Conservation.Finite
import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Consistency
import MarkovTriple.BGL.Theory.Compact.Gradient

/-!
# Non-vacuity: compact triples are complete

For a compact triple `1 ∈ 𝒜 = 𝒜₀` and `Γ(1) = 0` (F6 with `k = 0`), so `ζ_k = 1` witnesses
`DiffusionTriple.IsComplete`.  (The hypothesis of Thm 3.3.23 is thus satisfiable; the non-compact
instances Lebesgue / OU are NOT proved complete here.)
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

theorem CompactTriple.isComplete (C : CompactTriple E) : C.toDiffusionTriple.IsComplete := by
  have h1A : (fun _ : E => (1 : ℝ)) ∈ C.A := C.A.one_mem
  have h1 : (fun _ : E => (1 : ℝ)) ∈ C.A₀ := (C.A_eq _).1 h1A
  have hΓ : C.toDiffusionTriple.ΓA (fun _ : E => (1 : ℝ)) (fun _ : E => (1 : ℝ)) =ᵐ[C.μ] 0 := by
    have key := C.diffusion_Γ_A 0 (fun _ => 1) contDiff_const (fun i => i.elim0) (fun i => i.elim0)
      (fun _ : E => (1 : ℝ)) h1A
    filter_upwards [key] with x hx
    simpa using hx
  refine ⟨fun _ _ => 1, fun _ => h1, fun _ => Filter.Eventually.of_forall fun _ => zero_le_one,
    fun _ => Filter.Eventually.of_forall fun _ => le_rfl,
    Filter.Eventually.of_forall fun _ => tendsto_const_nhds, fun k => ?_⟩
  filter_upwards [hΓ, C.toDiffusionTriple.ΓA_ae_eq h1 h1] with x h2 h3
  have : C.toDiffusionTriple.Γ (fun _ : E => (1 : ℝ)) (fun _ : E => (1 : ℝ)) x = 0 := by
    rw [← h3]; exact h2
  show C.toDiffusionTriple.Γ (fun _ : E => (1 : ℝ)) (fun _ : E => (1 : ℝ)) x ≤ _
  rw [this]; positivity

/-- The weak gradient bound holds (unconditionally) for compact triples with `CD(ρ,n)`: the hypothesis
`HasGradientBound` of the mass-conservation theorems is satisfiable. -/
theorem CompactTriple.hasGradientBound {ρ : ℝ} {n : ENNReal} (C : CompactTriple E)
    (hCD : C.toFullTriple.CD ρ n) :
    HasGradientBound C.toDiffusionTriple C.A ρ :=
  C.toFullTriple.hasGradientBound hCD (compact_gradientInterpolation C)

end MarkovTriple.BGL
