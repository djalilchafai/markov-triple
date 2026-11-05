import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Atlas.Chart3Ops

/-!
# The glued operators of `sphereAtlas` are `ΓS`, `LS` of the genuine sphere `Sph 3` (Round 29, stream R, R1)
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.SphereN.Atlas

open MarkovTriple.BGL.Instances.Riemannian.R27
open LebesgueRd

theorem smooth_of_A₀S {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (k : ℕ) :
    sphereAtlas.Smooth k (fun p => f (eS2 p)) := by
  intro b
  show ContDiffOn ℝ k ((fun p => f (eS2 p)) ∘ ptS b) Set.univ
  have e : ((fun p => f (eS2 p)) ∘ ptS b) = fun y => ext f (Pc b y) := comp_eq f b
  rw [e]
  have hE : ContDiffOn ℝ k (ext f) {y | y ≠ 0} :=
    (show SmO (ext f) from hf).of_le (by exact_mod_cast le_top)
  have hP : ContDiff ℝ k (fun y => Pc b y) := contDiff_pi.2 fun a => contDiff_Pc b a k
  exact hE.comp hP.contDiffOn fun y _ => Pc_ne b y

theorem glueΓ_eq_ΓS {f h : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (hh : h ∈ A₀S 3) :
    sphereAtlas.glueΓ (fun p => f (eS2 p)) (fun p => h (eS2 p)) = fun p => ΓS f h (eS2 p) := by
  funext p
  have hp := sphereAtlas.pt_pos p
  change ((sph (sphereAtlas.idx p)).pt (sphereAtlas.pos p)) = p at hp
  exact (chart_Γ_eq hf hh (sphereAtlas.idx p) (sphereAtlas.pos p)).trans
    (congrArg (fun q => ΓS f h (eS2 q)) hp)

theorem glueL_eq_LS {f : Sph 3 → ℝ} (hf : f ∈ A₀S 3) :
    sphereAtlas.glueL (fun p => f (eS2 p)) = fun p => LS f (eS2 p) := by
  funext p
  have hp := sphereAtlas.pt_pos p
  change ((sph (sphereAtlas.idx p)).pt (sphereAtlas.pos p)) = p at hp
  exact (chart_L_eq hf (sphereAtlas.idx p) (sphereAtlas.pos p)).trans
    (congrArg (fun q => LS f (eS2 q)) hp)

theorem glue_eq_sphereDiffusion {f h : Sph 3 → ℝ} (hf : f ∈ A₀S 3) (hh : h ∈ A₀S 3) :
    sphereAtlas.glueΓ (f ∘ eS2) (h ∘ eS2) = (sphereDiffusion 3 (by norm_num)).Γ f h ∘ eS2 ∧
    sphereAtlas.glueL (f ∘ eS2) = (sphereDiffusion 3 (by norm_num)).L f ∘ eS2 := by
  rw [sphereDiffusion_Γ, sphereDiffusion_L]
  exact ⟨glueΓ_eq_ΓS hf hh, glueL_eq_LS hf⟩

end MarkovTriple.BGL.SphereN.Atlas
