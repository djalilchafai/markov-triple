import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Homog

/-!
# `𝒜₀ = C^∞(S^{n-1})` and the intrinsic operators `Γ`, `L` (Round 28, stream L, group L1)
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

/-- `𝒜₀ = 𝒜 = C^∞(S^{n-1})`: functions whose degree-0 extension is `C^∞` off the origin. -/
def A₀S (n : ℕ) : Subalgebra ℝ (Sph n → ℝ) where
  carrier := {f | SmO (ext f)}
  mul_mem' := fun {f g} hf hg => by
    show SmO (ext (f * g))
    rw [ext_mul]; exact SmO.mul hf hg
  add_mem' := fun {f g} hf hg => by
    show SmO (ext (f + g))
    rw [ext_add]; exact SmO.add hf hg
  algebraMap_mem' := fun r => by
    show SmO (ext (fun _ : Sph n => r))
    refine (contDiffOn_const (c := r)).congr fun y hy => ?_
    exact ext_of_ne _ hy

lemma mem_A₀S {f : Sph n → ℝ} : f ∈ A₀S n ↔ SmO (ext f) := Iff.rfl

/-- the carré du champ `Γ(f,g) = ∇F̃ · ∇G̃` of the degree-0 extensions, on the sphere. -/
noncomputable def ΓS (f g : Sph n → ℝ) : Sph n → ℝ :=
  fun x => LebesgueRd.Gf (ext f) (ext g) (cv (x : Ee n))

/-- the generator `L f = Δ F̃` of the degree-0 extension, on the sphere. -/
noncomputable def LS (f : Sph n → ℝ) : Sph n → ℝ :=
  fun x => LebesgueRd.Lf (ext f) (cv (x : Ee n))

lemma cv_proj (y : Fin n → ℝ) (hy : y ≠ 0) : cv ((proj y hy : Sph n) : Ee n) = (nrm y)⁻¹ • y := by
  funext i
  rw [show cv ((proj y hy : Sph n) : Ee n) i = ((proj y hy : Sph n) : Ee n) i from rfl,
    proj_coe_apply]
  rfl

lemma ext_ΓS {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ext (ΓS f g) y = LebesgueRd.sq y * LebesgueRd.Gf (ext f) (ext g) y := by
  rw [ext_of_ne _ hy]
  unfold ΓS Gf
  rw [cv_proj y hy]
  have hpos := nrm_pos hy
  have h1 : ∀ (F : Sph n → ℝ), F ∈ A₀S n → ∀ i, dd i (ext F) ((nrm y)⁻¹ • y) = nrm y * dd i (ext F) y := by
    intro F hF i
    have := hom_dd hF (hom_ext F) i ((nrm y)⁻¹) (inv_pos.2 hpos) y hy
    rw [this]
    simp
  simp only [h1 f hf, h1 g hg, ← nrm_sq]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ext_LS {f : Sph n → ℝ} (hf : f ∈ A₀S n) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ext (LS f) y = LebesgueRd.sq y * LebesgueRd.Lf (ext f) y := by
  rw [ext_of_ne _ hy]
  unfold LS Lf
  rw [cv_proj y hy]
  have hpos := nrm_pos hy
  have h2 : ∀ i, dd i (dd i (ext f)) ((nrm y)⁻¹ • y) = (nrm y) ^ 2 * dd i (dd i (ext f)) y := by
    intro i
    have := hom_dd (hf.ddO i) (hom_dd hf (hom_ext f) i) i ((nrm y)⁻¹) (inv_pos.2 hpos) y hy
    rw [this]
    simp
  simp only [h2, ← nrm_sq]
  rw [Finset.mul_sum]

lemma smO_Gf {F G : (Fin n → ℝ) → ℝ} (hF : SmO F) (hG : SmO G) : SmO (Gf F G) :=
  SmO.sum fun i => SmO.mul (hF.ddO i) (hG.ddO i)

lemma smO_Lf {F : (Fin n → ℝ) → ℝ} (hF : SmO F) : SmO (Lf F) :=
  SmO.sum fun i => (hF.ddO i).ddO i

theorem ΓS_mem {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) : ΓS f g ∈ A₀S n := by
  show SmO (ext (ΓS f g))
  have : SmO (fun y => LebesgueRd.sq y * Gf (ext f) (ext g) y) :=
    SmO.mul (SmO.of_sm sq_smooth) (smO_Gf hf hg)
  exact this.congr fun y hy => ext_ΓS hf hg hy

theorem LS_mem {f : Sph n → ℝ} (hf : f ∈ A₀S n) : LS f ∈ A₀S n := by
  show SmO (ext (LS f))
  have : SmO (fun y => LebesgueRd.sq y * Lf (ext f) y) :=
    SmO.mul (SmO.of_sm sq_smooth) (smO_Lf hf)
  exact this.congr fun y hy => ext_LS hf hy

/-- restrictions of `C^∞(ℝ^n)` functions lie in `𝒜₀`. -/
theorem A₀S_of_contDiff {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (fun x : Sph n => F (cv (x : Ee n))) ∈ A₀S n := by
  show SmO (ext fun x : Sph n => F (cv (x : Ee n)))
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => (nrm y)⁻¹ • y) {y | y ≠ 0} := by
    refine contDiffOn_pi.2 fun i => ?_
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => (nrm y)⁻¹) {y | y ≠ 0} :=
      smO_nrm.inv fun y hy => (nrm_pos hy).ne'
    exact h1.mul (contDiff_apply ℝ ℝ i).contDiffOn
  have := hF.comp_contDiffOn hv
  refine this.congr fun y hy => ?_
  rw [ext_of_ne _ hy, cv_proj y hy]
  rfl

end MarkovTriple.BGL.SphereN
