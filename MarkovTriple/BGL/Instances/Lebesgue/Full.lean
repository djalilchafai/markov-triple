import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Identify
import MarkovTriple.BGL.Instances.Lebesgue.Ergodic
import MarkovTriple.BGL.Instances.Lebesgue.FullEasy
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Semigroup.Conservative

/-!
# The Brownian triple on `(ℝ, Lebesgue)` as a `FullTriple` (BGL Def. 3.3.25), and `CD(0,∞)`

`𝒜₀ = C_c^∞(ℝ)`, `𝒜 = C^∞(ℝ)`, `L f = f''`, `Γ(f,g) = f' g'`; all of D1–D8, S10, S11, F1–F10
are proved (see `Identify.lean` for the heat-kernel identification used for S11 and F8).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

theorem semigroup_eq_heat {f : ℝ → ℝ} (hf : f ∈ A₀) (t : ℝ≥0) :
    lebesgueDiffusion.semigroup t (lebesgueDiffusion.cls ⟨f, hf⟩) =
      heatL2 (isTest_of hf) (Real.sqrt (2 * t)) := by
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h0 | hpos
  · subst h0
    have : DiffusionTriple.semigroup lebesgueDiffusion 0 = 1 :=
      (DiffusionTriple.formData lebesgueDiffusion).semigroup_zero
    rw [this]
    simp only [ContinuousLinearMap.one_apply, NNReal.coe_zero, mul_zero, Real.sqrt_zero]
    exact (heatL2_zero hf).symm
  · rw [← sub_eq_zero]
    refine lebesgueDiffusion.eq_zero_of_orth _ (fun g => ?_)
    rw [inner_sub_left, sub_eq_zero]
    have := inner_semigroup_heat hf g.2 (t := (t : ℝ)) (by exact_mod_cast hpos)
    rw [Real.toNNReal_coe] at this
    exact this

lemma semigroup_ae_heat {f : ℝ → ℝ} (hf : f ∈ A₀) (t : ℝ≥0) :
    (lebesgueDiffusion.semigroup t (lebesgueDiffusion.cls ⟨f, hf⟩) : ℝ → ℝ) =ᵐ[volume]
      heatM (Real.sqrt (2 * t)) f := by
  rw [semigroup_eq_heat hf t]
  exact (isTest_of hf).memLp_heatM _ |>.coeFn_toLp

theorem conservative_lebesgue (u : ℕ → ℝ → ℝ) (hu : IsExhaustion volume A₀ u)
    (hnn : ∀ n, 0 ≤ᵐ[volume] u n) (t : ℝ≥0) :
    ∀ᵐ x ∂(volume : Measure ℝ), Tendsto (fun n => (lebesgueDiffusion.semigroup t
      (lebesgueDiffusion.cls ⟨u n, hu.1 n⟩) : ℝ → ℝ) x) atTop (𝓝 1) := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n, (lebesgueDiffusion.semigroup t
      (lebesgueDiffusion.cls ⟨u n, hu.1 n⟩) : ℝ → ℝ) x = heatM (Real.sqrt (2 * t)) (u n) x :=
    ae_all_iff.2 fun n => semigroup_ae_heat (hu.1 n) t
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h0 | hpos
  · subst h0
    have e : DiffusionTriple.semigroup lebesgueDiffusion 0 = 1 :=
      (DiffusionTriple.formData lebesgueDiffusion).semigroup_zero
    have hc : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n, (lebesgueDiffusion.cls ⟨u n, hu.1 n⟩ : ℝ → ℝ) x = u n x :=
      ae_all_iff.2 fun n => lebesgueDiffusion.coeFn_cls ⟨u n, hu.1 n⟩
    filter_upwards [hc, hu.2.2] with x h1 h2
    simp only [e, ContinuousLinearMap.one_apply]
    exact h2.congr (fun n => (h1 n).symm)
  · have ha : Real.sqrt (2 * (t : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < t := by exact_mod_cast hpos
      exact (Real.sqrt_pos.2 (by linarith)).ne'
    have hle : ∀ n, ∀ᵐ y ∂(volume : Measure ℝ), |u n y| ≤ 1 := by
      intro n
      filter_upwards [hu.le_one_ae, hnn n] with y h1 h2
      rw [abs_of_nonneg h2]; exact h1 n
    filter_upwards [hae] with x hx
    have := heatM_tendsto_one ha (fun n => (smooth (hu.1 n)).continuous.measurable) hle hu.2.2 x
    exact this.congr (fun n => (hx n).symm)

/-- **The Brownian full triple on `(ℝ, Lebesgue)`.** -/
noncomputable def lebesgueFull : FullTriple ℝ where
  toStandardTriple :=
    { toDiffusionTriple := lebesgueDiffusion
      ergodic := fun u hu h => ergodic_lebesgue u hu h
      conservative := fun u hu hnn t => conservative_lebesgue u hu hnn t }
  A := A
  A₀_le := fun f hf => A₀_le_A hf
  A_measurable := fun f hf => (mem_A.1 hf).continuous.measurable
  ideal := fun f hf h hh => F1 hf hh
  pos_detect := fun f hf h => F2 hf h
  A_comp := fun k ψ hψ f hf => A_comp ψ hψ f hf
  L_mem_A := fun f hf => L_mem_A hf
  ΓA_nonneg := fun f hf => F5 hf
  diffusion_Γ_A := fun k ψ hψ f hf g hg => F6Γ k ψ hψ f hf hg
  diffusion_L_A := fun k ψ hψ f hf => F6L k ψ hψ f hf
  ibp_A := fun f hf g hg => F7 hf hg
  semigroup_A := fun t f => by
    refine ⟨heatM (Real.sqrt (2 * t)) f.1, (isTest_of f.2).heatM_contDiff _, ?_⟩
    exact semigroup_ae_heat f.2 t
  connected := fun f hf h => F9 hf h
  esa := fun u hu => esa_lebesgue u hu

lemma Γ₂_eq {f : ℝ → ℝ} (hf : Sm f) (x : ℝ) :
    lebesgueDiffusion.Γ₂ f f x = (Lf f x) ^ 2 := by
  have e : lebesgueDiffusion.ΓA f f = Gf f f := ΓA_eq_Gf hf hf
  have h1 : lebesgueDiffusion.ΓA f (lebesgueDiffusion.L f) = Gf f (Lf f) := ΓA_eq_Gf hf hf.deriv'.deriv'
  show (Lf (lebesgueDiffusion.ΓA f f) x - lebesgueDiffusion.ΓA f (Lf f) x
    - lebesgueDiffusion.ΓA (Lf f) f x) / 2 = _
  have h2 : lebesgueDiffusion.ΓA (Lf f) f = Gf (Lf f) f := ΓA_eq_Gf hf.deriv'.deriv' hf
  rw [e, h2, show lebesgueDiffusion.ΓA f (Lf f) = Gf f (Lf f) from h1]
  have h3 := Lf_mul hf.deriv' hf.deriv' x
  have : Gf f f = deriv f * deriv f := rfl
  rw [this, h3]
  simp only [Gf, Lf]
  ring

/-- **`CD(0,∞)`** (Def. 3.3.14, on all of `𝒜`), and more generally `CD(ρ, n)` for `ρ ≤ 0`,
`1 ≤ n ≤ ∞`; in particular `CD(0,1)`. -/
theorem lebesgue_CD {ρ : ℝ} (hρ : ρ ≤ 0) {n : ℝ≥0∞} (hn : 1 ≤ n) : lebesgueFull.CD ρ n := by
  refine ⟨hn, fun f hf => Filter.Eventually.of_forall fun x => ?_⟩
  have hf' : Sm f := mem_A.1 hf
  have hG : lebesgueFull.toDiffusionTriple.Γ₂ f f x = (Lf f x) ^ 2 := Γ₂_eq hf' x
  rw [hG]
  have h1 : (n⁻¹).toReal ≤ 1 := by
    have : n⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hn
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  have h2 : ρ * lebesgueFull.toDiffusionTriple.ΓA f f x ≤ 0 := by
    have : 0 ≤ lebesgueFull.toDiffusionTriple.ΓA f f x := by
      show 0 ≤ lebesgueDiffusion.ΓA f f x
      rw [ΓA_eq_Gf hf' hf']
      simpa [Gf] using mul_self_nonneg (deriv f x)
    exact mul_nonpos_of_nonpos_of_nonneg hρ this
  have h3 : (n⁻¹).toReal * (lebesgueFull.L f x) ^ 2 ≤ (Lf f x) ^ 2 := by
    show (n⁻¹).toReal * (Lf f x) ^ 2 ≤ (Lf f x) ^ 2
    nlinarith [sq_nonneg (Lf f x), ENNReal.toReal_nonneg (a := n⁻¹)]
  linarith

theorem lebesgue_CD_zero_infty : lebesgueFull.CD 0 ∞ := lebesgue_CD le_rfl le_top
theorem lebesgue_CD_zero_one : lebesgueFull.CD 0 1 := lebesgue_CD le_rfl le_rfl

end MarkovTriple.BGL.Lebesgue

#print axioms MarkovTriple.BGL.Lebesgue.lebesgueFull
#print axioms MarkovTriple.BGL.Lebesgue.lebesgue_CD
