import Mathlib
import MarkovTriple.BGL.Theory.Interp.Orbit

/-!
# `L¹`-differentiability of `s ↦ Γ(P_s f)` (analytic input of BGL Lemma 3.3.20 / proof of Thm 3.3.18)

`gammaE` is a bounded bilinear map `K × K → L¹` on the Hilbert space `K` of `𝒟(ℰ)` (`GB`); the orbit `s ↦ P_s f` is
`K`-differentiable (`hasDerivAt_cK`, from the graph-norm bound `‖v‖_K ≤ ‖v‖₂ + ‖Lv‖₂`), hence `s ↦ Γ(P_s f)` is
`L¹`-differentiable with derivative `2 Γ(P_s f, P_s L f)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- `gammaE` on `K` (bilinear). -/
noncomputable def GBl : KE T →ₗ[ℝ] KE T →ₗ[ℝ] Lp ℝ 1 T.μ :=
  LinearMap.mk₂ ℝ (fun x y => gammaE T ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv x)
    ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv y))
    (fun x x' y => by
      have := gammaE_lin_left (T := T) (u := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv x)
        (u' := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv x')
        (w := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv (x + x'))
        (v := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv y) 1 (by simp; erw [one_smul]; rfl)
      simpa using this)
    (fun c x y => by
      have h0 : gammaE T (0 : T.formDomain) ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv y) = 0 := by
        have := gammaE_lin_left (T := T) (u := 0) (u' := 0) (w := 0)
          (v := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv y) 1 (by simp)
        simpa using this
      have := gammaE_lin_left (T := T) (u := 0) (u' := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv x)
        (w := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv (c • x))
        (v := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv y) c (by simp; rfl)
      rw [h0, zero_add] at this
      simpa using this)
    (fun x y y' => by
      have := gammaE_lin_right (T := T) (v := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv y)
        (v' := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv y')
        (w := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv (y + y'))
        (u := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv x) 1 (by simp; erw [one_smul]; rfl)
      simpa using this)
    (fun c x y => by
      have h0 : gammaE T ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv x) (0 : T.formDomain) = 0 := by
        have := gammaE_lin_right (T := T) (v := 0) (v' := 0) (w := 0)
          (u := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv x) 1 (by simp)
        simpa using this
      have := gammaE_lin_right (T := T) (v := 0) (v' := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv y)
        (w := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv (c • y))
        (u := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv x) c (by simp; rfl)
      rw [h0, zero_add] at this
      simpa using this)

/-- `gammaE` as a continuous bilinear map `K × K → L¹`. -/
noncomputable def GB : KE T →L[ℝ] KE T →L[ℝ] Lp ℝ 1 T.μ :=
  LinearMap.mkContinuous₂ (GBl T) 1 (fun x y => by
    have := gammaE_bound (T := T) ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv x)
      ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv y)
    simpa [GBl] using this)

lemma GB_apply (u v : T.formDomain) :
    GB T ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u)
      ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm v) = gammaE T u v := by
  show gammaE T ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv
    ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u)) _ = _
  erw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- the `K`-valued orbit. -/
noncomputable def cK (ψ : T.A₀) (s : ℝ) : KE T :=
  (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm (T.orbQ ψ s)

/-- graph norm bound: `‖v‖_K ≤ ‖v‖₂ + ‖Lv‖₂` for `v ∈ 𝒟(L)`. -/
lemma kn_dom_le (d : T.toDiffusionTriple.generator.domain) :
    T.kn ⟨(d : Lp ℝ 2 T.μ), ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form d.2).1⟩ ≤
      ‖(d : Lp ℝ 2 T.μ)‖ + ‖T.toDiffusionTriple.generator d‖ := by
  have h := T.kn_sq_le d.2
  have h0 : 0 ≤ T.kn ⟨(d : Lp ℝ 2 T.μ),
      ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form d.2).1⟩ := norm_nonneg _
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  nlinarith [norm_nonneg (d : Lp ℝ 2 T.μ), norm_nonneg (T.toDiffusionTriple.generator d)]

/-- the orbit as an element of the domain of `L`. -/
noncomputable def orbD (ψ : T.A₀) (s : ℝ) : T.toDiffusionTriple.generator.domain :=
  ⟨T.orb ψ s, (T.orb_mem_dom ψ s).1⟩

lemma generator_orbD (ψ : T.A₀) (s : ℝ) :
    T.toDiffusionTriple.generator (T.orbD ψ s) = T.orb (T.Lt ψ) s := (T.orb_mem_dom ψ s).2

/-- `‖Sq a‖ ≤ ‖a‖₂ + ‖L a‖₂` for a domain element `a`. -/
lemma norm_cK_le (d : T.toDiffusionTriple.generator.domain) :
    ‖(DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm
      ⟨(d : Lp ℝ 2 T.μ), ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form d.2).1⟩‖ ≤
      ‖(d : Lp ℝ 2 T.μ)‖ + ‖T.toDiffusionTriple.generator d‖ := T.kn_dom_le d

/-- **The orbit is `K`-continuous.** -/
theorem continuous_cK (ψ : T.A₀) : Continuous (T.cK ψ) := by
  rw [continuous_iff_continuousAt]
  intro σ
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have c1 : Tendsto (fun σ' => ‖T.orb ψ σ' - T.orb ψ σ‖) (𝓝 σ) (𝓝 0) := by
    simpa using tendsto_iff_norm_sub_tendsto_zero.1 ((T.continuous_orb ψ).tendsto σ)
  have c2 : Tendsto (fun σ' => ‖T.orb (T.Lt ψ) σ' - T.orb (T.Lt ψ) σ‖) (𝓝 σ) (𝓝 0) := by
    simpa using tendsto_iff_norm_sub_tendsto_zero.1 ((T.continuous_orb (T.Lt ψ)).tendsto σ)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun σ' => ?_) (by simpa using c1.add c2)
  have hd : T.orbD ψ σ' - T.orbD ψ σ ∈ (⊤ : Set _) := trivial
  have := T.norm_cK_le (T.orbD ψ σ' - T.orbD ψ σ)
  have e1 : (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm
      ⟨((T.orbD ψ σ' - T.orbD ψ σ : T.toDiffusionTriple.generator.domain) : Lp ℝ 2 T.μ),
        ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form
          (T.orbD ψ σ' - T.orbD ψ σ).2).1⟩ = T.cK ψ σ' - T.cK ψ σ := by
    show (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm (T.orbQ ψ σ' - T.orbQ ψ σ) = _
    exact map_sub (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm _ _
  rw [e1] at this
  have e2 : ((T.orbD ψ σ' - T.orbD ψ σ : T.toDiffusionTriple.generator.domain) : Lp ℝ 2 T.μ) =
      T.orb ψ σ' - T.orb ψ σ := rfl
  have e3 : T.toDiffusionTriple.generator (T.orbD ψ σ' - T.orbD ψ σ) =
      T.orb (T.Lt ψ) σ' - T.orb (T.Lt ψ) σ := by
    rw [LinearPMap.map_sub, generator_orbD, generator_orbD]
  rw [e2, e3] at this
  exact this


/-- **`K`-differentiability of the orbit** (`σ > 0`). -/
theorem hasDerivAt_cK (ψ : T.A₀) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (T.cK ψ) (T.cK (T.Lt ψ) σ) σ := by
  have h1 := hasDerivAt_iff_isLittleO.1 (T.hasDerivAt_orb ψ hσ)
  have h2 := hasDerivAt_iff_isLittleO.1 (T.hasDerivAt_orb (T.Lt ψ) hσ)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Asymptotics.isLittleO_iff.1 h1 (half_pos hc),
    Asymptotics.isLittleO_iff.1 h2 (half_pos hc)] with σ' a1 a2
  set d : T.toDiffusionTriple.generator.domain :=
    T.orbD ψ σ' - T.orbD ψ σ - (σ' - σ) • T.orbD (T.Lt ψ) σ with hd
  have := T.norm_cK_le d
  have e1 : (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm
      ⟨(d : Lp ℝ 2 T.μ), ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form d.2).1⟩ =
      T.cK ψ σ' - T.cK ψ σ - (σ' - σ) • T.cK (T.Lt ψ) σ := by
    show (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm
      (T.orbQ ψ σ' - T.orbQ ψ σ - (σ' - σ) • T.orbQ (T.Lt ψ) σ) = _
    exact (map_sub (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm _ _).trans
      (congrArg₂ (· - ·) (map_sub (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm _ _)
        (map_smul (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm _ _))
  have e2 : (d : Lp ℝ 2 T.μ) = T.orb ψ σ' - T.orb ψ σ - (σ' - σ) • T.orb (T.Lt ψ) σ := rfl
  have e3 : T.toDiffusionTriple.generator d = T.orb (T.Lt ψ) σ' - T.orb (T.Lt ψ) σ -
      (σ' - σ) • T.orb (T.Lt (T.Lt ψ)) σ := by
    rw [hd, LinearPMap.map_sub, LinearPMap.map_sub, LinearPMap.map_smul, generator_orbD,
      generator_orbD, generator_orbD]
  rw [e1, e2, e3] at this
  linarith

lemma norm_GB_le (x y : KE T) : ‖GB T x y‖ ≤ ‖x‖ * ‖y‖ := by
  have := gammaE_bound (T := T) ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv x)
    ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv y)
  simpa [GB, GBl] using this

/-- the curve `s ↦ Γ(P_s f)` in `L¹`, `Γ(P_s f) = GB(cK s, cK s)` (`σ > 0`). -/
theorem hasDerivAt_uK (ψ : T.A₀) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun r => GB T (T.cK ψ r) (T.cK ψ r))
      (GB T (T.cK (T.Lt ψ) σ) (T.cK ψ σ) + GB T (T.cK ψ σ) (T.cK (T.Lt ψ) σ)) σ := by
  have hd := hasDerivAt_iff_isLittleO.1 (T.hasDerivAt_cK ψ hσ)
  have hcont := (T.continuous_cK ψ).tendsto σ
  set b := T.cK ψ σ with hb
  set d := T.cK (T.Lt ψ) σ with hdd
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hnb : 0 < 2 * ‖b‖ + 1 := by positivity
  have hnd : 0 < ‖d‖ + 1 := by positivity
  have hsmall : ∀ᶠ r in 𝓝 σ, ‖T.cK ψ r - b‖ ≤ min 1 (c / (3 * (‖d‖ + 1))) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hcont)
    exact this.eventually (Iic_mem_nhds (lt_min one_pos (by positivity)))
  filter_upwards [Asymptotics.isLittleO_iff.1 hd (by positivity : 0 < c / (3 * (2 * ‖b‖ + 1))),
    hsmall] with r hw hs
  set a := T.cK ψ r with ha
  set δ := r - σ with hδ
  set w := a - b - δ • d with hw0
  have eq : GB T a a - GB T b b - δ • (GB T d b + GB T b d) =
      δ • GB T d (a - b) + GB T w a + GB T b w := by
    simp only [hw0, map_sub, map_smul, sub_apply, smul_apply]
    module
  show ‖GB T a a - GB T b b - δ • (GB T d b + GB T b d)‖ ≤ c * ‖δ‖
  rw [eq]
  have h1 : ‖δ • GB T d (a - b)‖ ≤ ‖δ‖ * (‖d‖ * ‖a - b‖) := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (norm_GB_le T _ _) (norm_nonneg _)
  have h2 : ‖GB T w a‖ ≤ ‖w‖ * ‖a‖ := norm_GB_le T _ _
  have h3 : ‖GB T b w‖ ≤ ‖b‖ * ‖w‖ := norm_GB_le T _ _
  have ha1 : ‖a‖ ≤ ‖b‖ + 1 := by
    have := norm_le_insert' a b
    linarith [(min_le_left _ _).trans' hs |>.trans (le_refl _)]
  have hs1 : ‖a - b‖ ≤ 1 := hs.trans (min_le_left _ _)
  have hs2 : ‖a - b‖ ≤ c / (3 * (‖d‖ + 1)) := hs.trans (min_le_right _ _)
  have hdab : ‖d‖ * ‖a - b‖ ≤ c / 3 := by
    have : ‖d‖ * ‖a - b‖ ≤ (‖d‖ + 1) * (c / (3 * (‖d‖ + 1))) :=
      mul_le_mul (by linarith) hs2 (norm_nonneg _) hnd.le
    have e : (‖d‖ + 1) * (c / (3 * (‖d‖ + 1))) = c / 3 := by field_simp
    linarith
  have hww : ‖w‖ * (‖a‖ + ‖b‖) ≤ c / 3 * ‖δ‖ := by
    have hw' : ‖w‖ ≤ c / (3 * (2 * ‖b‖ + 1)) * ‖δ‖ := by simpa [hw0, hδ] using hw
    have : ‖w‖ * (‖a‖ + ‖b‖) ≤ (c / (3 * (2 * ‖b‖ + 1)) * ‖δ‖) * (2 * ‖b‖ + 1) :=
      mul_le_mul hw' (by linarith) (by positivity) (by positivity)
    have e : (c / (3 * (2 * ‖b‖ + 1)) * ‖δ‖) * (2 * ‖b‖ + 1) = c / 3 * ‖δ‖ := by field_simp
    linarith
  calc ‖δ • GB T d (a - b) + GB T w a + GB T b w‖
      ≤ ‖δ • GB T d (a - b)‖ + ‖GB T w a‖ + ‖GB T b w‖ := norm_add₃_le
    _ ≤ ‖δ‖ * (c / 3) + ‖w‖ * (‖a‖ + ‖b‖) := by nlinarith [norm_nonneg δ, norm_nonneg w]
    _ ≤ c * ‖δ‖ := by nlinarith [norm_nonneg δ]

theorem continuous_uK (ψ : T.A₀) : Continuous (fun r => GB T (T.cK ψ r) (T.cK ψ r)) := by
  have h := T.continuous_cK ψ
  exact ((GB T).continuous.comp h).clm_apply h

end FullTriple

end MarkovTriple.BGL
