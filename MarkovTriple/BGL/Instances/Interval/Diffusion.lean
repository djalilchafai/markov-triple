import Mathlib
import MarkovTriple.BGL.Instances.Interval.Basic
import MarkovTriple.BGL.Instances.Lebesgue.Diffusion
import MarkovTriple.BGL.Frozen.CD

/-!
# The interval triple `((0,1), Lebesgue)` as a `DiffusionTriple` (I1) and its `Γ₂`/curvature (I2)

See `STATEMENTS_R21_Interval.md`.  `𝒜₀ = C_c^∞((0,1))`, `L f = f''`, `Γ(f,g) = f' g'`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.Interval

lemma zero_off {f : ℝ → ℝ} (hf : f ∈ ivA₀) {x : ℝ} (hx : x ∉ Ioo (0 : ℝ) 1) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hf.2 h))

/-- integrals of functions vanishing off `(0,1)` over `ivμ` and over `volume` agree. -/
lemma integral_iv {h : ℝ → ℝ} (hh : ∀ x ∉ Ioo (0 : ℝ) 1, h x = 0) :
    ∫ x, h x ∂ivμ = ∫ x, h x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero hh

instance isProb_ivμ : IsProbabilityMeasure ivμ :=
  ⟨by simp [Real.volume_Ioo]⟩

/-- **The interval triple `((0,1), Lebesgue)`** (I1): `𝒜₀ = C_c^∞((0,1))`, `L f = f''`,
`Γ(f,g) = f' g'`. -/
@[reducible] noncomputable def ivDiff : MarkovTriple.BGL.DiffusionTriple ℝ where
  μ := ivμ
  sigmaFinite := inferInstance
  finite_prob := fun _ => isProb_ivμ
  A₀ := ivA₀
  measurable := fun f hf => (ivA₀_smooth hf).continuous.measurable
  bounded := fun f hf => by
    obtain ⟨C, hC⟩ := (ivA₀_smooth hf).continuous.bounded_above_of_compact_support (ivA₀_cs hf)
    exact ⟨C, fun x => by simpa using hC x⟩
  memLp := fun f hf p _ _ => (Lebesgue.memLp_of (ivA₀_le hf) p).restrict _
  dense := fun p hp hp' => by
    have := hp
    exact ivA₀_dense p hp'
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_ivA₀ k ψ hψ h0 f hf
  exhaustion := ⟨ivcut, ivcut_mem, fun n => Filter.Eventually.of_forall fun x => ivcut_mono n x,
    (ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall fun _ hx => ivcut_tendsto hx)⟩
  Γ := Lebesgue.Gf
  L := Lebesgue.Lf
  Γ_mem := fun f hf g hg => mul_mem (deriv_mem_ivA₀ hf) (deriv_mem_ivA₀ hg)
  L_mem := fun f hf => deriv_mem_ivA₀ (deriv_mem_ivA₀ hf)
  Γ_symm := fun f _ g _ => Filter.Eventually.of_forall fun x => by simp [Lebesgue.Gf, mul_comm]
  Γ_add := fun f hf f' hf' g _ => Filter.Eventually.of_forall fun x => by
    simp [Lebesgue.Gf, Lebesgue.deriv_add_sm hf.1 hf'.1, add_mul]
  Γ_smul := fun c f hf g _ => Filter.Eventually.of_forall fun x => by
    simp [Lebesgue.Gf, Lebesgue.deriv_smul_sm c hf.1, mul_assoc]
  Γ_nonneg := fun f _ => Filter.Eventually.of_forall fun x => by
    simpa [Lebesgue.Gf] using mul_self_nonneg (deriv f x)
  diffusion := fun k ψ hψ _ f hf g _ =>
    Filter.Eventually.of_forall fun x => by
      have := congrFun ((Lebesgue.diffusion_c k ψ hψ f (fun i => (hf i).1)).1 g) x
      simpa using this
  ibp := fun f hf g hg => by
    have h := Lebesgue.ibp_L hf.1 (ivA₀_le hg)
    have e1 : ∫ x, g x * Lebesgue.Lf f x ∂ivμ = ∫ x, g x * Lebesgue.Lf f x :=
      integral_iv fun x hx => by simp [zero_off hg hx]
    have e2 : ∫ x, Lebesgue.Gf f g x ∂ivμ = ∫ x, Lebesgue.Gf f g x :=
      integral_iv fun x hx => by
        simp [Lebesgue.Gf, zero_off (deriv_mem_ivA₀ hg) hx]
    rw [e1, e2]; exact h
  integral_L := fun f hf => by
    have e : ∫ x, Lebesgue.Lf f x ∂ivμ = ∫ x, Lebesgue.Lf f x :=
      integral_iv fun x hx => zero_off (deriv_mem_ivA₀ (deriv_mem_ivA₀ hf)) hx
    rw [e]; exact Lebesgue.integral_Lf (ivA₀_le hf)

/-! ### `Γ₂` and curvature (I2) -/

/-- `ΓA(f,g) = f' g'` for smooth `f, g` (the formula-defined `Γ`). -/
lemma iv_ΓA {f g : ℝ → ℝ} (hf : Lebesgue.Sm f) (hg : Lebesgue.Sm g) (x : ℝ) :
    ivDiff.ΓA f g x = deriv f x * deriv g x := by
  show (Lebesgue.Lf (f * g) x - f x * Lebesgue.Lf g x - g x * Lebesgue.Lf f x) / 2 = _
  rw [Lebesgue.Lf_mul hf hg]; ring

/-- **I2**: `Γ₂(f) = (f'')²` pointwise for every smooth `f`. -/
theorem iv_Γ₂_eq {f : ℝ → ℝ} (hf : Lebesgue.Sm f) (x : ℝ) :
    ivDiff.Γ₂ f f x = (deriv (deriv f) x) ^ 2 := by
  have e1 : ivDiff.ΓA f f = fun y => deriv f y * deriv f y := funext fun y => iv_ΓA hf hf y
  have hLf : Lebesgue.Sm (Lebesgue.Lf f) := hf.deriv'.deriv'
  have e2 : ivDiff.ΓA f (Lebesgue.Lf f) x = deriv f x * deriv (deriv (deriv f)) x := by
    rw [iv_ΓA hf hLf]; rfl
  have e3 : ivDiff.ΓA (Lebesgue.Lf f) f x = deriv f x * deriv (deriv (deriv f)) x := by
    rw [iv_ΓA hLf hf, mul_comm]; rfl
  have h1 : deriv (fun y => deriv f y * deriv f y) = fun y => 2 * (deriv f y * deriv (deriv f) y) := by
    funext y
    have := ((hf.deriv'.hasDerivAt y).mul (hf.deriv'.hasDerivAt y))
    refine Eq.trans this.deriv ?_
    ring
  have h2 : deriv (fun y => 2 * (deriv f y * deriv (deriv f) y)) x =
      2 * (deriv (deriv f) x * deriv (deriv f) x + deriv f x * deriv (deriv (deriv f)) x) := by
    have := ((hf.deriv'.hasDerivAt x).mul (hf.deriv'.deriv'.hasDerivAt x)).const_mul 2
    exact this.deriv
  show (Lebesgue.Lf (ivDiff.ΓA f f) x - ivDiff.ΓA f (Lebesgue.Lf f) x -
    ivDiff.ΓA (Lebesgue.Lf f) f x) / 2 = _
  rw [e1, e2, e3]
  unfold Lebesgue.Lf
  rw [h1, h2]; ring

/-- The curvature-dimension inequality for the interval triple, in the shape of `FullTriple.CD`
(`FullTriple.CD` itself is unavailable: by `iv_no_fullTriple` there is no `FullTriple` over `ivDiff`).
The candidate extended algebra is `C^∞`; the inequality is pointwise. -/
def IvCD (ρ : ℝ) (n : ℝ≥0∞) : Prop :=
  1 ≤ n ∧ ∀ f : ℝ → ℝ, Lebesgue.Sm f → ∀ x : ℝ,
    ρ * ivDiff.ΓA f f x + (n⁻¹).toReal * (ivDiff.L f x) ^ 2 ≤ ivDiff.Γ₂ f f x

/-- **I2**: `CD(ρ, n)` holds for every `ρ ≤ 0` and every `n ∈ [1, ∞]` (in particular `CD(0, n)`). -/
theorem ivDiff_CD {ρ : ℝ} {n : ℝ≥0∞} (hρ : ρ ≤ 0) (hn : 1 ≤ n) : IvCD ρ n := by
  refine ⟨hn, fun f hf x => ?_⟩
  rw [iv_Γ₂_eq hf, iv_ΓA hf hf]
  have h1 : (n⁻¹).toReal ≤ 1 := by
    have : n⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hn
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  have h0 : 0 ≤ (n⁻¹).toReal := ENNReal.toReal_nonneg
  have hL : ivDiff.L f x = deriv (deriv f) x := rfl
  rw [hL]
  nlinarith [mul_self_nonneg (deriv f x), mul_self_nonneg (deriv (deriv f) x),
    mul_nonneg h0 (sq_nonneg (deriv (deriv f) x)),
    mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (deriv (deriv f) x)),
    mul_nonneg (neg_nonneg.2 hρ) (mul_self_nonneg (deriv f x))]

end MarkovTriple.BGL.Instances.Interval
