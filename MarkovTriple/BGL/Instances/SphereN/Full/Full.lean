import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Curv2
import MarkovTriple.BGL.Instances.SphereN.Full.Spectral
import MarkovTriple.BGL.Instances.LebesgueRd.FullEasy
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Theory.Extension.R26.Core2Eigen
import MarkovTriple.BGL.Semigroup.Characterization

/-!
# The Full Markov Triple of the round sphere, conditionally on F8 (Round 29, stream N, group N4)

`sphereFull hn h8 : FullTriple (Sph n)` with `𝒜 = 𝒜₀ = C^∞(S^{n-1})`.  Every field is proved except F8,
which is the hypothesis `SphereF8 n hn` (a `Prop`, not an axiom).  `CD(n-2, n-1)` and `Core2` follow.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma hat_eq_of_far {F : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} (hz : 3 / 10 < nrm z) : hat F z = F z := by
  show chi (nrm z) * F z = F z
  rw [chi_of_ge hz.le, one_mul]

lemma ne_zero_of_far {z : Fin n → ℝ} (hz : 3 / 10 < nrm z) : z ≠ 0 := by
  rintro rfl
  have h0 : nrm (0 : Fin n → ℝ) = 0 := by simp [nrm]
  rw [h0] at hz; norm_num at hz

lemma ext_comp_ev {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (f : Fin k → Sph n → ℝ) {y : Fin n → ℝ}
    (hy : 3 / 10 < nrm y) :
    ext (fun x => ψ (fun j => f j x)) =ᶠ[𝓝 y] fun z => ψ (fun j => hat (ext (f j)) z) := by
  filter_upwards [isOpen_far.mem_nhds hy] with z hz
  have hz0 := ne_zero_of_far hz
  simp only [ext_of_ne _ hz0, hat_eq_of_far hz]

theorem A₀S_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → Sph n → ℝ) (hf : ∀ j, f j ∈ A₀S n) :
    (fun x => ψ (fun j => f j x)) ∈ A₀S n := by
  show SmO (ext fun x => ψ (fun j => f j x))
  refine (SmO.comp ψ hψ (fun j => ext (f j)) hf).congr fun y hy => ?_
  simp only [ext_of_ne _ (show y ≠ 0 from hy)]

lemma val_hat {F : Sph n → ℝ} (x : Sph n) : hat (ext F) (cv (x : Ee n)) = F x := by
  rw [hat_eq_of_far (sphere_far x), ext_cv]

theorem ΓS_comp_gen {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → Sph n → ℝ) (hf : ∀ j, f j ∈ A₀S n) (g : Sph n → ℝ) (x : Sph n) :
    ΓS (fun x => ψ (fun j => f j x)) g x
      = ∑ j, pderiv ψ j (fun l => f l x) * ΓS (f j) g x := by
  have hfar := sphere_far x
  set y := cv (x : Ee n) with hy
  show Gf (ext fun x => ψ (fun j => f j x)) (ext g) y = _
  rw [Gf_congr (ext_comp_ev ψ f hfar) (Filter.EventuallyEq.refl _ _)]
  have := congrFun (Gf_comp ψ hψ (fun j => hat (ext (f j))) (fun j => Sm_hat (hf j)) (ext g)) y
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (fun l => hat (ext (f l)) y) = fun l => f l x := funext fun l => val_hat x
  rw [e1]
  congr 1
  exact Gf_congr (hat_ev hfar) (Filter.EventuallyEq.refl _ _)

theorem LS_comp_gen {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → Sph n → ℝ) (hf : ∀ j, f j ∈ A₀S n) (x : Sph n) :
    LS (fun x => ψ (fun j => f j x)) x
      = ∑ j, pderiv ψ j (fun l => f l x) * LS (f j) x +
        ∑ j, ∑ l, pderiv₂ ψ j l (fun m => f m x) * ΓS (f j) (f l) x := by
  have hfar := sphere_far x
  set y := cv (x : Ee n) with hy
  show Lf (ext fun x => ψ (fun j => f j x)) y = _
  rw [Lf_congr (ext_comp_ev ψ f hfar)]
  have := congrFun (Lf_comp ψ hψ (fun j => hat (ext (f j))) (fun j => Sm_hat (hf j))) y
  rw [this]
  have e1 : (fun l => hat (ext (f l)) y) = fun l => f l x := funext fun l => val_hat x
  simp only [e1]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact Lf_congr (hat_ev hfar)
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    exact Gf_congr (hat_ev hfar) (hat_ev hfar)

/-- positivity detection (F2) for the sphere. -/
lemma pos_detect_S {f : Sph n → ℝ} (hf : f ∈ A₀S n)
    (h : ∀ g ∈ A₀S n, 0 ≤ᵐ[σ n] g → 0 ≤ ∫ x, g x * f x ∂σ n) : 0 ≤ᵐ[σ n] f := by
  have hfc : Continuous f := continuous_of_mem hf
  set ψ : (Fin 1 → ℝ) → ℝ := fun v => Real.smoothTransition (-(v 0)) with hψ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (Real.smoothTransition.contDiff.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).neg))
  set m : Sph n → ℝ := fun x => Real.smoothTransition (-(f x)) with hm
  have hmem : m ∈ A₀S n := A₀S_comp ψ hψs (f := fun _ : Fin 1 => f) (fun _ => hf)
  have hmc : Continuous m := Real.smoothTransition.continuous.comp hfc.neg
  have hm0 : ∀ x, 0 ≤ m x := fun x => Real.smoothTransition.nonneg _
  have hmf : ∀ x, m x * f x ≤ 0 := by
    intro x
    rcases le_total 0 (f x) with h1 | h1
    · have : m x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [this]; simp
    · exact mul_nonpos_of_nonneg_of_nonpos (hm0 x) h1
  have hpair := h m hmem (Eventually.of_forall hm0)
  have hint : Integrable (fun x => m x * f x) (σ n) :=
    (memLp_of_mem (mul_mem hmem hf) 1).integrable le_rfl
  have h0 : ∫ x, -(m x * f x) ∂σ n = 0 := by
    have : ∫ x, m x * f x ∂σ n ≤ 0 := integral_nonpos fun x => hmf x
    have h2 : ∫ x, m x * f x ∂σ n = 0 := le_antisymm this hpair
    rw [integral_neg, h2, neg_zero]
  have := (integral_eq_zero_iff_of_nonneg (fun x => neg_nonneg.2 (hmf x)) hint.neg).1 h0
  filter_upwards [this] with x hx
  by_contra hneg
  push Not at hneg
  have hpos : 0 < m x := Real.smoothTransition.pos_of_pos (by simp only [Pi.zero_apply] at hneg; linarith)
  have : -(m x * f x) = 0 := hx
  have : m x * f x = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · simp only [Pi.zero_apply] at hneg; linarith

/-- **F8** for the round sphere: `P_t f ∈ 𝒜 = C^∞(S^{n-1})` for `f ∈ 𝒜₀`, `t ≥ 0` (a hypothesis, NOT proved). -/
def SphereF8 (n : ℕ) (hn : 2 ≤ n) : Prop := ∀ (t : ℝ≥0) (f : (sphereDiffusion n hn).A₀), ∃ g ∈ A₀S n,
    ((sphereDiffusion n hn).semigroup t ((sphereDiffusion n hn).cls f) : Sph n → ℝ) =ᵐ[σ n] g

/-- **The Full Markov Triple of the round sphere `S^{n-1}`, conditionally on F8.** -/
noncomputable def sphereFull (hn : 2 ≤ n) (h8 : SphereF8 n hn) : FullTriple (Sph n) where
  toStandardTriple := sphereStandard hn
  A := A₀S n
  A₀_le := fun f hf => hf
  A_measurable := fun f hf => (continuous_of_mem hf).measurable
  ideal := fun f hf h hh => mul_mem hh hf
  pos_detect := fun f hf h => pos_detect_S hf h
  A_comp := fun k ψ hψ f hf => A₀S_comp ψ hψ f hf
  L_mem_A := fun f hf => LS_mem hf
  ΓA_nonneg := fun f hf => Eventually.of_forall fun x => by
    show 0 ≤ (sphereDiffusion n hn).ΓA f f x
    rw [ΓA_eq_ΓS hn hf hf]
    exact ΓS_nonneg f x
  diffusion_Γ_A := fun k ψ hψ f hf g hg => Eventually.of_forall fun x => by
    have hc := A₀S_comp ψ hψ f hf
    show (sphereDiffusion n hn).ΓA (fun x => ψ (fun i => f i x)) g x = _
    rw [ΓA_eq_ΓS hn hc hg, ΓS_comp_gen ψ hψ f hf g x]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = _ * (sphereDiffusion n hn).ΓA (f i) g x
    rw [ΓA_eq_ΓS hn (hf i) hg]
  diffusion_L_A := fun k ψ hψ f hf => Eventually.of_forall fun x => by
    show LS (fun x => ψ (fun i => f i x)) x = _
    rw [LS_comp_gen ψ hψ f hf x]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show _ = _ * (sphereDiffusion n hn).ΓA (f i) (f j) x
    rw [ΓA_eq_ΓS hn (hf i) (hf j)]
  ibp_A := fun f hf g hg => by
    have e := ΓA_eq_ΓS hn hf hg
    have h1 := ibp_sphere (n := n) (by omega) hf hg
    have h2 := ibp_sphere (n := n) (by omega) hg hf
    rw [ΓS_symm g f] at h2
    show (∫ x, (sphereDiffusion n hn).ΓA f g x ∂σ n = -∫ x, g x * LS f x ∂σ n) ∧
      (∫ x, (sphereDiffusion n hn).ΓA f g x ∂σ n = -∫ x, f x * LS g x ∂σ n)
    rw [e]
    exact ⟨by linarith, by linarith⟩
  semigroup_A := h8
  connected := fun f hf hΓ => by
    have e := ΓA_eq_ΓS hn hf hf
    let F : (sphereDiffusion n hn).A₀ := ⟨f, hf⟩
    have hΓ0 : (sphereDiffusion n hn).Γ F.1 F.1 =ᵐ[(sphereDiffusion n hn).μ] 0 := by
      have : (sphereDiffusion n hn).Γ F.1 F.1 = (sphereDiffusion n hn).ΓA F.1 F.1 := by rw [e]
      rw [this]; exact hΓ
    have hE : (sphereStandard hn).toDiffusionTriple.closedForm
        ⟨(sphereDiffusion n hn).cls F,
          (DiffusionTriple.formData (sphereDiffusion n hn)).emb_mem_Q
            ⟨DiffusionTriple.clsₗ (sphereDiffusion n hn) F, ⟨F, rfl⟩⟩⟩
        ⟨(sphereDiffusion n hn).cls F,
          (DiffusionTriple.formData (sphereDiffusion n hn)).emb_mem_Q
            ⟨DiffusionTriple.clsₗ (sphereDiffusion n hn) F, ⟨F, rfl⟩⟩⟩ = 0 :=
      (DiffusionTriple.closedForm_cls (sphereDiffusion n hn) F F).trans
        ((DiffusionTriple.energy_zero_iff (sphereDiffusion n hn) F).2 hΓ0)
    obtain ⟨c, hc⟩ := StandardTriple.energy_zero_const (sphereStandard hn)
      ⟨(sphereDiffusion n hn).cls F,
        (DiffusionTriple.formData (sphereDiffusion n hn)).emb_mem_Q
          ⟨DiffusionTriple.clsₗ (sphereDiffusion n hn) F, ⟨F, rfl⟩⟩⟩ hE
    exact ⟨c, (DiffusionTriple.coeFn_cls (sphereDiffusion n hn) F).symm.trans hc⟩
  esa := fun u hu => sphere_esa hn u hu

lemma sphereFull_μ (hn : 2 ≤ n) (h8 : SphereF8 n hn) : (sphereFull hn h8).μ = σ n := rfl

/-- **`CD(n-2, n-1)` for the Full triple of the round sphere** (BGL Appendix C.5). -/
theorem sphereFull_CD (hn : 2 ≤ n) (h8 : SphereF8 n hn) :
    (sphereFull hn h8).CD ((n : ℝ) - 2) ((n : ℝ≥0∞) - 1) := by
  have h2 : (2 : ℝ≥0∞) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) - 1 := by
    refine ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top ?_
    simpa [one_add_one_eq_two] using h2
  refine ⟨h1, fun f hf => Eventually.of_forall fun x => ?_⟩
  have e1 : (((n : ℝ≥0∞) - 1)⁻¹).toReal = 1 / ((n : ℝ) - 1) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le (by exact_mod_cast (by omega : 1 ≤ n))
      (ENNReal.natCast_ne_top n)]
    simp
  have hA := ΓA_eq_ΓS hn (f := f) (g := f) hf hf
  show ((n : ℝ) - 2) * (sphereDiffusion n hn).ΓA f f x + (((n : ℝ≥0∞) - 1)⁻¹).toReal * (LS f x) ^ 2 ≤ _
  rw [e1, hA]
  exact sphere_CD hn hf x

/-- **`Core2` for the Full triple of the round sphere**, from the eigenbasis criterion. -/
theorem sphereFull_core2 (hn : 2 ≤ n) (h8 : SphereF8 n hn) : (sphereFull hn h8).Core2 := by
  refine FullTriple.core2_of_eigen' (T := sphereFull hn h8) (harmSet n hn) ?_ (dense_span_harm hn)
  rintro φ ⟨k, h, hh, hφ⟩
  refine ⟨lamS n k, lamS_nonneg hn k, Eventually.of_forall fun x => ?_⟩
  have hfA : φ = hA hn h := Subtype.ext hφ
  subst hfA
  exact L_hA hn hh x

end MarkovTriple.BGL.SphereN
