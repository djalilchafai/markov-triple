import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Spectral
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-!
# The zonal sphere `S³` as a `DiffusionTriple` (D1–D8)
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm deriv_comp1 contDiff_pderiv)
open MarkovTriple.BGL (pderiv pderiv₂)

namespace MarkovTriple.BGL.Instances.Sphere

lemma vec_eq_ext {k : ℕ} (f : Fin k → Zon → ℝ) (x : Zon) :
    (fun j => f j x) = fun j => ext (f j) (arc x) := funext fun j => apply_eq_ext _ x

lemma comp_mem_AZ {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {f : Fin k → Zon → ℝ}
    (hf : ∀ i, f i ∈ AZ) : (fun x => ψ (fun i => f i x)) ∈ AZ := by
  show Sm (ext (fun x => ψ (fun i => f i x)))
  exact hψ.comp (contDiff_pi.2 fun i => (hf i : Sm (ext (f i))))

lemma GZ_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {f : Fin k → Zon → ℝ}
    (hf : ∀ i, f i ∈ AZ) (g : Zon → ℝ) (x : Zon) :
    GZ (fun y => ψ (fun i => f i y)) g x =
      ∑ i, pderiv ψ i (fun j => f j x) * GZ (f i) g x := by
  have hsm : ∀ i, Sm (ext (f i)) := fun i => hf i
  have e : ext (fun y => ψ (fun i => f i y)) = fun θ => ψ (fun i => ext (f i) θ) := rfl
  simp only [GZ_apply, dG, e]
  rw [deriv_comp1 ψ hψ (fun i => ext (f i)) hsm, vec_eq_ext f x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma LZ_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {f : Fin k → Zon → ℝ}
    (hf : ∀ i, f i ∈ AZ) (x : Zon) :
    LZ (fun y => ψ (fun i => f i y)) x =
      ∑ i, pderiv ψ i (fun j => f j x) * LZ (f i) x +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * GZ (f i) (f j) x := by
  have hsm : ∀ i, Sm (ext (f i)) := fun i => hf i
  have e : ext (fun y => ψ (fun i => f i y)) = fun θ => ψ (fun i => ext (f i) θ) := rfl
  rw [LZ_apply, e, dL_comp ψ hψ hsm (fun i => ep_ext (f i)), vec_eq_ext f x]
  rfl

lemma GZ_symm (f g : Zon → ℝ) : GZ f g = GZ g f := by
  funext x; simp only [GZ_apply, dG]; ring

lemma GZ_add {f f' g : Zon → ℝ} (hf : f ∈ AZ) (hf' : f' ∈ AZ) (x : Zon) :
    GZ (f + f') g x = GZ f g x + GZ f' g x := by
  have e : ext (f + f') = ext f + ext f' := rfl
  have h := MarkovTriple.Sanity.OU.deriv_add_s (show Sm (ext f) from hf) (show Sm (ext f') from hf')
  simp only [GZ_apply, dG, e, h, Pi.add_apply]; ring

lemma GZ_smul (c : ℝ) {f g : Zon → ℝ} (hf : f ∈ AZ) (x : Zon) :
    GZ (c • f) g x = c * GZ f g x := by
  have e : ext (c • f) = c • ext f := rfl
  have h := MarkovTriple.Sanity.OU.deriv_smul_s c (show Sm (ext f) from hf)
  simp only [GZ_apply, dG, e, h, Pi.smul_apply, smul_eq_mul]; ring

lemma GZ_const (f : Zon → ℝ) (c : ℝ) : GZ f (fun _ => c) = 0 := by
  funext x
  have : deriv (ext fun _ : Zon => c) = 0 := by
    have : ext (fun _ : Zon => c) = fun _ => c := rfl
    rw [this]; exact deriv_const' c
  simp [GZ_apply, dG, this]

lemma integral_LZ {f : Zon → ℝ} (hf : f ∈ AZ) : ∫ x, LZ f x ∂μZ = 0 := by
  have h1 : (1 : Zon → ℝ) ∈ AZ := AZ.one_mem
  have := ibpZ hf h1
  simp only [Pi.one_apply, one_mul] at this
  rw [this]
  have h2 : GZ f 1 = 0 := GZ_const f 1
  rw [h2]; simp

/-- The zonal sphere `S³` as a Diffusion Markov Triple. -/
noncomputable abbrev sT : MarkovTriple.BGL.DiffusionTriple Zon where
  μ := μZ
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := A0Z
  measurable := fun f hf => (continuous_of_mem hf).measurable
  bounded := fun f hf => bounded_of_mem hf
  memLp := fun f hf p _ _ => memLp_of_mem hf p
  dense := fun p hp hp' => by
    have := hp
    exact dense_Lp p hp'
  comp_mem := fun k ψ hψ _ f hf => comp_mem_AZ ψ hψ hf
  exhaustion := ⟨fun _ _ => 1, fun _ => AZ.one_mem,
    fun _ => Filter.Eventually.of_forall fun _ => le_refl _,
    Filter.Eventually.of_forall fun _ => tendsto_const_nhds⟩
  Γ := GZ
  L := LZ
  Γ_mem := fun f hf g hg => GZ_mem hf hg
  L_mem := fun f hf => LZ_mem hf
  Γ_symm := fun f _ g _ => Filter.Eventually.of_forall fun x => by rw [GZ_symm]
  Γ_add := fun f hf f' hf' g _ => Filter.Eventually.of_forall fun x => GZ_add hf hf' x
  Γ_smul := fun c f hf g _ => Filter.Eventually.of_forall fun x => GZ_smul c hf x
  Γ_nonneg := fun f _ => Filter.Eventually.of_forall fun x => by
    simp only [GZ_apply, dG, Pi.zero_apply]; exact mul_self_nonneg _
  diffusion := fun k ψ hψ _ f hf g _ => Filter.Eventually.of_forall fun x => GZ_comp ψ hψ hf g x
  ibp := fun f hf g hg => ibpZ hf hg
  integral_L := fun f hf => integral_LZ hf

end MarkovTriple.BGL.Instances.Sphere
