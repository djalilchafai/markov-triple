import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple
import MarkovTriple.Sanity.Circle

/-!
# The circle satisfies the data D1–D8 of a Diffusion Markov Triple (NOT frozen)

Re-uses the (old, pointwise) circle computations of `Sanity/Circle.lean`: Haar probability measure,
`𝒜₀ = C^∞(𝕋)`, `L f = f''`, `Γ(f,g) = f' g'`.  New items relative to the old surface: boundedness
(continuity on a compact space), the exhaustion sequence `u_n = 1` (constants are smooth), D8
(`∫ f'' = 0`), `finite_prob` (Haar measure is a probability measure).  This is a `DiffusionTriple`
only; a full instance proof (S10, S11, F1–F10 with `𝒜 = C^∞(𝕋) = 𝒜₀`) is a later stage.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BGL.Sanity

open MarkovTriple.Sanity.Circle

/-- The circle as a Diffusion Markov Triple. -/
noncomputable def circleDiffusion : DiffusionTriple 𝕋 where
  μ := μ₀
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := _root_.MarkovTriple.Sanity.Circle.A₀
  measurable := fun f hf => (A₀_prop hf).2.2.measurable
  bounded := fun f hf => by
    obtain ⟨C, hC⟩ := bound_of_continuous (_root_.MarkovTriple.Sanity.Circle.continuous_of_A₀ hf)
    exact ⟨C, fun x => by simpa using hC x⟩
  memLp := fun f hf p _ _ => memLp_of_mem hf p
  dense := fun p hp hp' => by
    have := hp
    exact dense_Lp p hp'
  comp_mem := fun k ψ hψ _ f hf => by
    rw [_root_.MarkovTriple.Sanity.Circle.mem_A₀]
    exact hψ.comp (contDiff_pi.2 fun i => _root_.MarkovTriple.Sanity.Circle.mem_A₀.1 (hf i))
  exhaustion := ⟨fun _ _ => 1, fun _ => _root_.MarkovTriple.Sanity.Circle.mem_A₀.2 contDiff_const,
    fun _ => Filter.Eventually.of_forall fun _ => le_refl _,
    Filter.Eventually.of_forall fun _ => tendsto_const_nhds⟩
  Γ := Gc
  L := Lc
  Γ_mem := fun f hf g hg => Gc_mem hf hg
  L_mem := fun f hf => Lc_mem hf
  Γ_symm := fun f _ g _ => Filter.Eventually.of_forall fun x => by simp [Gc, mul_comm]
  Γ_add := fun f hf f' hf' g _ => Filter.Eventually.of_forall fun x => by
    simp [Gc, D_add (Sm_of_mem hf) (Sm_of_mem hf'), add_mul]
  Γ_smul := fun c f hf g _ => Filter.Eventually.of_forall fun x => by
    simp [Gc, D_smul c (Sm_of_mem hf), mul_assoc]
  Γ_nonneg := fun f _ => Filter.Eventually.of_forall fun x => by
    simpa [Gc] using mul_self_nonneg (D f x)
  diffusion := fun k ψ hψ h0 f hf g hg =>
    ((diffusion_c k ψ hψ f hf).1 g hg).eventuallyEq
  ibp := fun f hf g hg => ibp_c hf hg
  integral_L := fun f hf => integral_D (D_mem hf)

end MarkovTriple.BGL.Sanity
