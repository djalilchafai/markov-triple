import Mathlib
import MarkovTriple.BGL.Instances.SphereOpen.Semi
import MarkovTriple.BGL.Instances.Sphere.Curvature
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Semigroup.Characterization

/-!
# The open zonal sphere as a Full Markov Triple, `CD(2,3)` (R17 Noncompact, N5, N6)

`oFull : FullTriple ZonO` with `ZonO = (-1,1)` a non-compact state space.  F1-F10, S10, S11 are theorems
(F8, F10, S10, S11 through the transport `Semi.lean`).  `CD(2,3)` is the Bakry-Émery value `CD(n-1,n)`,
`n = 3`, of `Instances/Sphere/Curvature.lean` (`Γ₂(f) = F''² + 2 (F'/sin θ)²`), transported pointwise.
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open MarkovTriple.BGL (pderiv pderiv₂)

namespace MarkovTriple.BGL.Instances.SphereOpen

open MarkovTriple.BGL.Instances.Sphere

lemma ΓA_eq_GO {f g : ZonO → ℝ} (hf : f ∈ AO) (hg : g ∈ AO) : oT.ΓA f g = GO f g := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨g, hg, rfl⟩ := hg
  funext x
  have e : (f ∘ jO) * (g ∘ jO) = (f * g) ∘ jO := rfl
  show (LO ((f ∘ jO) * (g ∘ jO)) x - (f ∘ jO) x * LO (g ∘ jO) x - (g ∘ jO) x * LO (f ∘ jO) x) / 2 =
    GO (f ∘ jO) (g ∘ jO) x
  rw [e, LO_comp (mul_mem hf hg), LO_comp hf, LO_comp hg, GO_comp hf hg]
  exact ΓA_eq hf hg (jO x)

lemma GO_diffusion {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {f0 : Fin k → Zon → ℝ} (hf0 : ∀ i, f0 i ∈ AZ) {g : Zon → ℝ} (hg : g ∈ AZ) (x : ZonO) :
    GO (fun x => ψ (fun i => (f0 i ∘ jO) x)) (g ∘ jO) x =
      ∑ i, pderiv ψ i (fun j => (f0 j ∘ jO) x) * GO (f0 i ∘ jO) (g ∘ jO) x := by
  have e : (fun x => ψ (fun i => (f0 i ∘ jO) x)) = (fun y => ψ (fun i => f0 i y)) ∘ jO := rfl
  rw [e, GO_comp (comp_mem_AZ ψ hψ hf0) hg]
  simp only [Function.comp_apply]
  rw [GZ_comp ψ hψ hf0 g (jO x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GO_comp (hf0 i) hg]
  rfl

/-- the open zonal sphere as a Standard Markov Triple (S10, S11). -/
noncomputable abbrev oStandard : StandardTriple ZonO where
  toDiffusionTriple := oT
  ergodic := fun u hu h => open_ergodic u hu h
  conservative := fun _ hu _ t =>
    DiffusionTriple.conservative_of_semigroup_one oT hu t (semigroup_one_O t)

/-- positivity detection (F2) for the open triple. -/
lemma pos_detect_O {f0 : Zon → ℝ} (hf0 : f0 ∈ AZ)
    (h : ∀ g ∈ oT.A₀, 0 ≤ᵐ[oT.μ] g → 0 ≤ ∫ x, g x * (f0 ∘ jO) x ∂oT.μ) : 0 ≤ᵐ[μO] (f0 ∘ jO) := by
  have h1 : 0 ≤ᵐ[μZ] f0 := by
    refine pos_detect_aux hf0 (fun g hg hgnn => ?_)
    have hgA : g ∈ AZ := hg
    have := h (g ∘ jO) (comp_mem_AO hgA) (ae_comap_jO (p := fun y => (0 : ℝ) ≤ g y) hgnn)
    have e := integral_comp_jO (fun y => g y * f0 y)
    exact e ▸ this
  exact ae_comap_jO (p := fun y => (0 : ℝ) ≤ f0 y) h1

/-- **The open zonal sphere `(-1,1)` as a Full Markov Triple.** -/
noncomputable abbrev oFull : FullTriple ZonO where
  toStandardTriple := oStandard
  A := AO
  A₀_le := fun f hf => mem_A0O.1 hf
  A_measurable := fun f hf => by
    obtain ⟨g, hg, rfl⟩ := hf
    exact ((continuous_of_mem hg).comp continuous_jO).measurable
  ideal := fun f hf h hh => mul_mem hh (show f ∈ A0O from hf)
  pos_detect := fun f hf h => by
    obtain ⟨f0, hf0, rfl⟩ := hf
    exact pos_detect_O hf0 h
  A_comp := fun k ψ hψ f hf => comp_mem_AO' ψ hψ hf
  L_mem_A := fun f hf => LO_mem hf
  ΓA_nonneg := fun f hf => by
    have e := ΓA_eq_GO hf hf
    obtain ⟨f0, hf0, rfl⟩ := hf
    exact Eventually.of_forall fun x => by
      show 0 ≤ oT.ΓA (f0 ∘ jO) (f0 ∘ jO) x
      rw [e, GO_comp hf0 hf0]
      simp only [Function.comp_apply, GZ_apply, dG]
      exact mul_self_nonneg _
  diffusion_Γ_A := fun k ψ hψ f hf g hg => by
    choose f0 hf0 hff using hf
    obtain ⟨g0, hg0, rfl⟩ := hg
    have ef : f = fun i => f0 i ∘ jO := funext hff
    subst ef
    have hc : (fun x => ψ (fun i => (f0 i ∘ jO) x)) ∈ AO := comp_mem_AO' ψ hψ (fun i => comp_mem_AO (hf0 i))
    refine Eventually.of_forall fun x => ?_
    show oT.ΓA (fun x => ψ (fun i => (f0 i ∘ jO) x)) (g0 ∘ jO) x = _
    rw [ΓA_eq_GO hc (comp_mem_AO hg0), GO_diffusion ψ hψ hf0 hg0 x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ΓA_eq_GO (comp_mem_AO (hf0 i)) (comp_mem_AO hg0)]
  diffusion_L_A := fun k ψ hψ f hf => by
    choose f0 hf0 hff using hf
    have ef : f = fun i => f0 i ∘ jO := funext hff
    subst ef
    refine Eventually.of_forall fun x => ?_
    have e : (fun x => ψ (fun i => (f0 i ∘ jO) x)) = (fun y => ψ (fun i => f0 i y)) ∘ jO := rfl
    show LO (fun x => ψ (fun i => (f0 i ∘ jO) x)) x = _
    rw [e, LO_comp (comp_mem_AZ ψ hψ hf0)]
    simp only [Function.comp_apply]
    rw [LZ_comp ψ hψ hf0 (jO x)]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [LO_comp (hf0 i)]
      rfl
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [ΓA_eq_GO (comp_mem_AO (hf0 i)) (comp_mem_AO (hf0 j)), GO_comp (hf0 i) (hf0 j)]
      rfl
  ibp_A := fun f hf g hg => by
    have e := ΓA_eq_GO hf (mem_A0O.1 hg)
    obtain ⟨f0, hf0, rfl⟩ := hf
    obtain ⟨g0, hg0, rfl⟩ := mem_A0O.1 hg
    have e2 : GO (f0 ∘ jO) (g0 ∘ jO) = fun x => GZ f0 g0 (jO x) := by
      rw [GO_comp hf0 hg0]; rfl
    have e2' : GO (g0 ∘ jO) (f0 ∘ jO) = fun x => GZ f0 g0 (jO x) := by
      rw [GO_comp hg0 hf0, GZ_symm]; rfl
    have e3 : (fun x => (g0 ∘ jO) x * LO (f0 ∘ jO) x) = fun x => (fun y => g0 y * LZ f0 y) (jO x) := by
      funext x; rw [LO_comp hf0]; rfl
    have e4 : (fun x => (f0 ∘ jO) x * LO (g0 ∘ jO) x) = fun x => (fun y => f0 y * LZ g0 y) (jO x) := by
      funext x; rw [LO_comp hg0]; rfl
    have h1 := ibpZ hf0 hg0
    have h2 := ibpZ hg0 hf0
    rw [GZ_symm g0 f0] at h2
    show (∫ x, oT.ΓA (f0 ∘ jO) (g0 ∘ jO) x ∂μO = -∫ x, (g0 ∘ jO) x * LO (f0 ∘ jO) x ∂μO) ∧
      (∫ x, oT.ΓA (f0 ∘ jO) (g0 ∘ jO) x ∂μO = -∫ x, (f0 ∘ jO) x * LO (g0 ∘ jO) x ∂μO)
    rw [e, e2, e3, e4, integral_comp_jO (GZ f0 g0), integral_comp_jO (fun y => g0 y * LZ f0 y),
      integral_comp_jO (fun y => f0 y * LZ g0 y)]
    exact ⟨by linarith, by linarith⟩
  semigroup_A := fun t f => by
    obtain ⟨g, hg, hae⟩ := semigroup_cls_mem_O t f
    exact ⟨g, hg, hae⟩
  connected := fun f hf hΓ => by
    have e := ΓA_eq_GO hf hf
    obtain ⟨f0, hf0, rfl⟩ := hf
    let F : oT.A₀ := ⟨f0 ∘ jO, comp_mem_AO hf0⟩
    have hΓ0 : oT.Γ F.1 F.1 =ᵐ[oT.μ] 0 := by
      have : oT.Γ F.1 F.1 = oT.ΓA F.1 F.1 := by rw [e]
      rw [this]; exact hΓ
    have hE : oStandard.toDiffusionTriple.closedForm
        ⟨oT.cls F, (DiffusionTriple.formData oT).emb_mem_Q ⟨DiffusionTriple.clsₗ oT F, ⟨F, rfl⟩⟩⟩
        ⟨oT.cls F, (DiffusionTriple.formData oT).emb_mem_Q ⟨DiffusionTriple.clsₗ oT F, ⟨F, rfl⟩⟩⟩
        = 0 := by
      exact (DiffusionTriple.closedForm_cls oT F F).trans
        ((DiffusionTriple.energy_zero_iff oT F).2 hΓ0)
    obtain ⟨c, hc⟩ := StandardTriple.energy_zero_const oStandard
      ⟨oT.cls F, (DiffusionTriple.formData oT).emb_mem_Q ⟨DiffusionTriple.clsₗ oT F, ⟨F, rfl⟩⟩⟩ hE
    exact ⟨c, (DiffusionTriple.coeFn_cls oT F).symm.trans hc⟩
  esa := fun u hu => DiffusionTriple.core_of_invariant oT semigroup_invariant_O u hu

lemma oFull_μ : oFull.μ = μO := rfl

instance : IsProbabilityMeasure oFull.μ := (inferInstance : IsProbabilityMeasure μO)

/-! ### `CD(2,3)` -/

lemma L_oFull {f0 : Zon → ℝ} (hf0 : f0 ∈ AZ) : oFull.L (f0 ∘ jO) = LZ f0 ∘ jO := LO_comp hf0

lemma Γ₂_O {f0 : Zon → ℝ} (hf0 : f0 ∈ AZ) (x : ZonO) :
    oT.Γ₂ (f0 ∘ jO) (f0 ∘ jO) x = sT.Γ₂ f0 f0 (jO x) := by
  have hG : GZ f0 f0 ∈ AZ := GZ_mem hf0 hf0
  have hL : LZ f0 ∈ AZ := LZ_mem hf0
  unfold DiffusionTriple.Γ₂
  have e1 : oT.ΓA (f0 ∘ jO) (f0 ∘ jO) = GZ f0 f0 ∘ jO := by
    rw [ΓA_eq_GO (comp_mem_AO hf0) (comp_mem_AO hf0), GO_comp hf0 hf0]
  have e2 : oT.L (f0 ∘ jO) = LZ f0 ∘ jO := LO_comp hf0
  have e3 : oT.ΓA (f0 ∘ jO) (LZ f0 ∘ jO) = GZ f0 (LZ f0) ∘ jO := by
    rw [ΓA_eq_GO (comp_mem_AO hf0) (comp_mem_AO hL), GO_comp hf0 hL]
  have e4 : oT.ΓA (LZ f0 ∘ jO) (f0 ∘ jO) = GZ (LZ f0) f0 ∘ jO := by
    rw [ΓA_eq_GO (comp_mem_AO hL) (comp_mem_AO hf0), GO_comp hL hf0]
  have s1 : sT.ΓA f0 f0 = GZ f0 f0 := ΓA_eq_GZ hf0 hf0
  have s3 : sT.ΓA f0 (sT.L f0) = GZ f0 (LZ f0) := ΓA_eq_GZ hf0 hL
  have s4 : sT.ΓA (sT.L f0) f0 = GZ (LZ f0) f0 := ΓA_eq_GZ hL hf0
  rw [e1, e2, e3, e4, s1, s3, s4]
  show (LO (GZ f0 f0 ∘ jO) x - (GZ f0 (LZ f0) ∘ jO) x - (GZ (LZ f0) f0 ∘ jO) x) / 2 =
    (LZ (GZ f0 f0) (jO x) - GZ f0 (LZ f0) (jO x) - GZ (LZ f0) f0 (jO x)) / 2
  rw [LO_comp hG]
  rfl

/-- **`CD(2,3)` on the open zonal sphere** (BGL's `CD(n-1,n)`, `n = 3`, `Γ₂` computation of the
Gegenbauer/sphere operator, transported to the non-compact state space `(-1,1)`). -/
theorem oFull_CD : oFull.CD 2 3 := by
  refine ⟨by norm_num, fun f hf => ?_⟩
  obtain ⟨f0, hf0, rfl⟩ := hf
  have h := (sphere_CD_two_three).2 f0 hf0
  filter_upwards [ae_comap_jO h] with x hx
  have e1 : oT.ΓA (f0 ∘ jO) (f0 ∘ jO) x = sT.ΓA f0 f0 (jO x) := by
    rw [ΓA_eq_GO (comp_mem_AO hf0) (comp_mem_AO hf0), GO_comp hf0 hf0, ΓA_eq_GZ hf0 hf0]
    rfl
  have e2 : oT.L (f0 ∘ jO) x = sT.L f0 (jO x) := by
    show LO (f0 ∘ jO) x = _
    rw [LO_comp hf0]; rfl
  have e3 := Γ₂_O hf0 x
  show 2 * oT.ΓA (f0 ∘ jO) (f0 ∘ jO) x + ((3 : ℝ≥0∞)⁻¹).toReal * (oT.L (f0 ∘ jO) x) ^ 2 ≤
    oT.Γ₂ (f0 ∘ jO) (f0 ∘ jO) x
  rw [e1, e2, e3]
  exact hx

end MarkovTriple.BGL.Instances.SphereOpen
