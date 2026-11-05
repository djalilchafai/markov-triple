import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Ibp

/-!
# The Diffusion Markov Triple on the genuine sphere `S^{n-1}` (Round 28, stream L, group L2)

`μ = σ` (normalised surface measure), `𝒜₀ = C^∞(S^{n-1})`, `Γ(f,g) = ∇F̃·∇G̃`, `L = ΔF̃` of the degree-0 extensions.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma ΓS_one (f : Sph n → ℝ) : ΓS f 1 = 0 := by
  funext x
  have hx := cv_ne_zero x
  have hu : ext (1 : Sph n → ℝ) =ᶠ[𝓝 (cv (x : Ee n))] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_ne0.mem_nhds hx] with z hz
    rw [ext_one]; simp [hz]
  have h0 : ∀ i, dd i (ext (1 : Sph n → ℝ)) (cv (x : Ee n)) = 0 := fun i => by
    rw [dd_congr hu i]; simp [dd]
  simp [ΓS, Gf, h0]

/-- **The Diffusion Markov Triple of the genuine round sphere `S^{n-1} ⊂ ℝ^n`** (`n ≥ 2`). -/
@[reducible] noncomputable def sphereDiffusion (n : ℕ) (hn : 2 ≤ n) : DiffusionTriple (Sph n) where
  μ := σ n
  sigmaFinite := inferInstance
  finite_prob := fun _ => σ_isProbabilityMeasure (by omega)
  A₀ := (A₀S n).toNonUnitalSubalgebra
  measurable := fun f hf => (continuous_of_mem hf).measurable
  bounded := fun f hf => bounded_of_mem hf
  memLp := fun f hf p _ _ => memLp_of_mem hf p
  dense := fun p hp hp' => by
    have := hp
    exact dense_Lp p hp'
  comp_mem := fun k ψ hψ h0 f hf => by
    show SmO (ext fun x => ψ (fun j => f j x))
    rw [ext_comp ψ h0 f]
    exact SmO.comp ψ hψ (fun j => ext (f j)) hf
  exhaustion := ⟨fun _ => 1, fun _ => (A₀S n).one_mem,
    fun _ => Eventually.of_forall fun _ => le_refl _,
    Eventually.of_forall fun _ => tendsto_const_nhds⟩
  Γ := ΓS
  L := LS
  Γ_mem := fun f hf g hg => ΓS_mem hf hg
  L_mem := fun f hf => LS_mem hf
  Γ_symm := fun f _ g _ => Eventually.of_forall fun x => by rw [ΓS_symm f g]
  Γ_add := fun f hf f' hf' g _ => Eventually.of_forall fun x => by rw [ΓS_add hf hf']
  Γ_smul := fun c f hf g _ => Eventually.of_forall fun x => by rw [ΓS_smul c hf]
  Γ_nonneg := fun f _ => Eventually.of_forall fun x => ΓS_nonneg f x
  diffusion := fun k ψ hψ h0 f hf g _ => Eventually.of_forall fun x => by
    rw [ΓS_comp ψ hψ h0 f hf g]
  ibp := fun f hf g hg => ibp_sphere (by omega) hf hg
  integral_L := fun f hf => by
    have := ibp_sphere (n := n) (by omega) hf (A₀S n).one_mem
    simpa [ΓS_one] using this

theorem sphereDiffusion_μ (hn : 2 ≤ n) : (sphereDiffusion n hn).μ = σ n := rfl
theorem sphereDiffusion_Γ (hn : 2 ≤ n) : (sphereDiffusion n hn).Γ = ΓS := rfl
theorem sphereDiffusion_L (hn : 2 ≤ n) : (sphereDiffusion n hn).L = LS := rfl

end MarkovTriple.BGL.SphereN
