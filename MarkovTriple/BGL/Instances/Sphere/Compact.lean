import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Semi
import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Frozen.Gamma2
import MarkovTriple.BGL.Consistency
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Characterization

/-!
# The zonal round sphere `S³` as a genuinely compact `CompactTriple`, `CD(2,3)`

`E = [-1,1]` (compact), `μ = (2/π)√(1-x²) dx` (the law of the first coordinate on `S³ ⊂ ℝ⁴` under the
normalised surface measure), `𝒜 = 𝒜₀ = {f | θ ↦ f(cos θ) smooth}`, `L f = (1-x²) f'' - 3 x f'`
(the Laplace–Beltrami operator on zonal functions), `Γ(f,g) = (1-x²) f'g'`.
Eigenfunctions: `U_k(x)` (Chebyshev, second kind), `L U_k = -k(k+2) U_k`.

Fields: `ΓA = Γ` (`ΓA_eq`); `CD(2,3)` (Bakry–Émery for `S^n`: `CD(n-1,n)`, `n = 3`) holds on all of `𝒜`.
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open MarkovTriple.Sanity.OU (Sm deriv_comp1 contDiff_pderiv)
open MarkovTriple.BGL (pderiv pderiv₂)

namespace MarkovTriple.BGL.Instances.Sphere

/-- `F : Zon → ℝ`, `F ∈ 𝒜` is positivity detected by `𝒜₀` (F2). -/
lemma pos_detect_aux {f : Zon → ℝ} (hf : f ∈ AZ)
    (h : ∀ g ∈ sT.A₀, 0 ≤ᵐ[sT.μ] g → 0 ≤ ∫ x, g x * f x ∂sT.μ) : 0 ≤ᵐ[μZ] f := by
  have hfc : Continuous f := continuous_of_mem hf
  set ψ : (Fin 1 → ℝ) → ℝ := fun v => Real.smoothTransition (-(v 0)) with hψ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (Real.smoothTransition.contDiff.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).neg))
  set m : Zon → ℝ := fun x => Real.smoothTransition (-(f x)) with hm
  have hmem : m ∈ AZ :=
    comp_mem_AZ ψ hψs (f := fun _ : Fin 1 => f) (fun _ => hf)
  have hmc : Continuous m := Real.smoothTransition.continuous.comp hfc.neg
  have hm0 : ∀ x, 0 ≤ m x := fun x => Real.smoothTransition.nonneg _
  have hmf : ∀ x, m x * f x ≤ 0 := by
    intro x
    rcases le_total 0 (f x) with h1 | h1
    · have : m x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [this]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos (hm0 x) h1
  have hpair := h m hmem (Eventually.of_forall hm0)
  have hint : Integrable (fun x => m x * f x) μZ := integrable_of_cont (hmc.mul hfc)
  have h0 : ∫ x, -(m x * f x) ∂μZ = 0 := by
    have : ∫ x, m x * f x ∂μZ ≤ 0 := integral_nonpos fun x => hmf x
    have h2 : ∫ x, m x * f x ∂μZ = 0 := le_antisymm this hpair
    rw [integral_neg, h2, neg_zero]
  have := (integral_eq_zero_iff_of_nonneg (fun x => neg_nonneg.2 (hmf x)) hint.neg).1 h0
  filter_upwards [this] with x hx
  by_contra hneg
  push_neg at hneg
  have hpos : 0 < m x := Real.smoothTransition.pos_of_pos (by simp only [Pi.zero_apply] at hneg; linarith)
  have : -(m x * f x) = 0 := hx
  have : m x * f x = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · simp only [Pi.zero_apply] at hneg; linarith

/-- the zonal sphere as a Standard Markov Triple. -/
noncomputable def sStandard : StandardTriple Zon where
  toDiffusionTriple := sT
  ergodic := fun u hu h => sphere_ergodic u hu h
  conservative := fun _ hu _ t =>
    DiffusionTriple.conservative_of_semigroup_one sT hu t (semigroup_one t)

lemma ΓA_eq_GZ {f g : Zon → ℝ} (hf : f ∈ AZ) (hg : g ∈ AZ) : sT.ΓA f g = GZ f g := by
  funext x
  exact ΓA_eq hf hg x

/-- The zonal sphere as a Full Markov Triple. -/
noncomputable def sFull : FullTriple Zon where
  toStandardTriple := sStandard
  A := AZ
  A₀_le := fun f hf => hf
  A_measurable := fun f hf => (continuous_of_mem hf).measurable
  ideal := fun f hf h hh => mul_mem hh hf
  pos_detect := fun f hf h => pos_detect_aux hf h
  A_comp := fun k ψ hψ f hf => comp_mem_AZ ψ hψ hf
  L_mem_A := fun f hf => LZ_mem hf
  ΓA_nonneg := fun f hf => Eventually.of_forall fun x => by
    show 0 ≤ sT.ΓA f f x
    rw [ΓA_eq_GZ hf hf]
    simp only [GZ_apply, dG]; exact mul_self_nonneg _
  diffusion_Γ_A := fun k ψ hψ f hf g hg => Eventually.of_forall fun x => by
    have hc := comp_mem_AZ ψ hψ hf
    show sT.ΓA (fun x => ψ (fun i => f i x)) g x = _
    rw [ΓA_eq_GZ hc hg, GZ_comp ψ hψ hf g x]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (ΓA_eq_GZ (hf i) hg) x
    show _ = _ * sT.ΓA (f i) g x
    rw [this]
  diffusion_L_A := fun k ψ hψ f hf => Eventually.of_forall fun x => by
    show LZ (fun x => ψ (fun i => f i x)) x = _
    rw [LZ_comp ψ hψ hf x]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (ΓA_eq_GZ (hf i) (hf j)) x
    show _ = _ * sT.ΓA (f i) (f j) x
    rw [this]
  ibp_A := fun f hf g hg => by
    have e := ΓA_eq_GZ hf hg
    have h1 := ibpZ hf hg
    have h2 := ibpZ hg hf
    rw [GZ_symm g f] at h2
    show (∫ x, sT.ΓA f g x ∂μZ = -∫ x, g x * LZ f x ∂μZ) ∧
      (∫ x, sT.ΓA f g x ∂μZ = -∫ x, f x * LZ g x ∂μZ)
    rw [e]
    exact ⟨by linarith, by linarith⟩
  semigroup_A := fun t f => by
    obtain ⟨g, hg, hae⟩ := semigroup_cls_mem t f
    exact ⟨g, hg, hae⟩
  connected := fun f hf hΓ => by
    have e := ΓA_eq_GZ hf hf
    let F : sT.A₀ := ⟨f, hf⟩
    have hΓ0 : sT.Γ f f =ᵐ[sT.μ] 0 := by
      have : sT.Γ f f = sT.ΓA f f := by rw [e]
      rw [this]; exact hΓ
    have hE : sStandard.toDiffusionTriple.closedForm
        ⟨sT.cls F, (DiffusionTriple.formData sT).emb_mem_Q ⟨DiffusionTriple.clsₗ sT F, ⟨F, rfl⟩⟩⟩
        ⟨sT.cls F, (DiffusionTriple.formData sT).emb_mem_Q ⟨DiffusionTriple.clsₗ sT F, ⟨F, rfl⟩⟩⟩
        = 0 := by
      exact (DiffusionTriple.closedForm_cls sT F F).trans
        ((DiffusionTriple.energy_zero_iff sT F).2 hΓ0)
    obtain ⟨c, hc⟩ := StandardTriple.energy_zero_const sStandard
      ⟨sT.cls F, (DiffusionTriple.formData sT).emb_mem_Q ⟨DiffusionTriple.clsₗ sT F, ⟨F, rfl⟩⟩⟩ hE
    exact ⟨c, (DiffusionTriple.coeFn_cls sT F).symm.trans hc⟩
  esa := fun u hu => DiffusionTriple.core_of_invariant sT semigroup_invariant u hu

/-- **The zonal round sphere `S³` as a genuinely compact Compact Markov Triple.** -/
noncomputable def sCompact : CompactTriple Zon where
  toFullTriple := sFull
  A_eq := fun _ => Iff.rfl

end MarkovTriple.BGL.Instances.Sphere
