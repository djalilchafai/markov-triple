import Mathlib
import MarkovTriple.BGL.Instances.IntervalGen.Dense
import MarkovTriple.BGL.Instances.Lebesgue.Diffusion
import MarkovTriple.BGL.Frozen.CD

/-!
# The triple `(Ω, normalised Lebesgue, C_c^∞(Ω))` for bounded open `Ω ⊆ ℝ` as a `DiffusionTriple` (G1) and its `Γ₂`/curvature (G2)

See `STATEMENTS_R22_E1.md`.  `L f = f''`, `Γ(f,g) = f' g'`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.IntervalGen

namespace BddOpen

variable (Ω : BddOpen)

/-- **G1**: the diffusion triple `(Ω, |Ω|⁻¹ dx, C_c^∞(Ω))`, `L = d²/dx²`, `Γ = f' g'`. -/
@[reducible] noncomputable def diff : MarkovTriple.BGL.DiffusionTriple ℝ where
  μ := Ω.μ
  sigmaFinite := inferInstance
  finite_prob := fun _ => Ω.isProb_μ
  A₀ := Ω.A₀
  measurable := fun f hf => (A₀_smooth hf).continuous.measurable
  bounded := fun f hf => by
    obtain ⟨C, hC⟩ := (A₀_smooth hf).continuous.bounded_above_of_compact_support (A₀_cs hf)
    exact ⟨C, fun x => by simpa using hC x⟩
  memLp := fun f hf p _ _ => (A₀_smooth hf).continuous.memLp_of_hasCompactSupport (A₀_cs hf)
  dense := fun p hp hp' => by
    have := hp
    exact Ω.A₀_dense p hp'
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_A₀ k ψ hψ h0 f hf
  exhaustion := ⟨Ω.cut, Ω.cut_mem, fun n => Filter.Eventually.of_forall fun x => Ω.cut_mono n x,
    (Ω.ae_μ_iff).2 (Filter.Eventually.of_forall fun _ hx => Ω.cut_tendsto hx)⟩
  Γ := Lebesgue.Gf
  L := Lebesgue.Lf
  Γ_mem := fun f hf g hg => mul_mem (deriv_mem_A₀ hf) (deriv_mem_A₀ hg)
  L_mem := fun f hf => deriv_mem_A₀ (deriv_mem_A₀ hf)
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
    have h := Lebesgue.ibp_L hf.1 (A₀_le hg)
    have e1 : ∫ x, g x * Lebesgue.Lf f x ∂Ω.μ =
        ((volume Ω.carrier)⁻¹).toReal * ∫ x, g x * Lebesgue.Lf f x :=
      Ω.integral_μ fun x hx => by simp [zero_off hg hx]
    have e2 : ∫ x, Lebesgue.Gf f g x ∂Ω.μ =
        ((volume Ω.carrier)⁻¹).toReal * ∫ x, Lebesgue.Gf f g x :=
      Ω.integral_μ fun x hx => by
        simp [Lebesgue.Gf, zero_off (deriv_mem_A₀ hg) hx]
    rw [e1, e2, h, mul_neg]
  integral_L := fun f hf => by
    have e : ∫ x, Lebesgue.Lf f x ∂Ω.μ = ((volume Ω.carrier)⁻¹).toReal * ∫ x, Lebesgue.Lf f x :=
      Ω.integral_μ fun x hx => zero_off (deriv_mem_A₀ (deriv_mem_A₀ hf)) hx
    rw [e, Lebesgue.integral_Lf (A₀_le hf), mul_zero]

/-! ### `Γ₂` and curvature (G2) -/

/-- `ΓA(f,g) = f' g'` for smooth `f, g`. -/
lemma ΓA_eq {f g : ℝ → ℝ} (hf : Lebesgue.Sm f) (hg : Lebesgue.Sm g) (x : ℝ) :
    Ω.diff.ΓA f g x = deriv f x * deriv g x := by
  show (Lebesgue.Lf (f * g) x - f x * Lebesgue.Lf g x - g x * Lebesgue.Lf f x) / 2 = _
  rw [Lebesgue.Lf_mul hf hg]; ring

/-- **G2**: `Γ₂(f) = (f'')²` pointwise for every smooth `f`. -/
theorem Γ₂_eq {f : ℝ → ℝ} (hf : Lebesgue.Sm f) (x : ℝ) :
    Ω.diff.Γ₂ f f x = (deriv (deriv f) x) ^ 2 := by
  have e1 : Ω.diff.ΓA f f = fun y => deriv f y * deriv f y := funext fun y => Ω.ΓA_eq hf hf y
  have hLf : Lebesgue.Sm (Lebesgue.Lf f) := hf.deriv'.deriv'
  have e2 : Ω.diff.ΓA f (Lebesgue.Lf f) x = deriv f x * deriv (deriv (deriv f)) x := by
    rw [Ω.ΓA_eq hf hLf]; rfl
  have e3 : Ω.diff.ΓA (Lebesgue.Lf f) f x = deriv f x * deriv (deriv (deriv f)) x := by
    rw [Ω.ΓA_eq hLf hf, mul_comm]; rfl
  have h1 : deriv (fun y => deriv f y * deriv f y) = fun y => 2 * (deriv f y * deriv (deriv f) y) := by
    funext y
    have := ((hf.deriv'.hasDerivAt y).mul (hf.deriv'.hasDerivAt y))
    refine Eq.trans this.deriv ?_
    ring
  have h2 : deriv (fun y => 2 * (deriv f y * deriv (deriv f) y)) x =
      2 * (deriv (deriv f) x * deriv (deriv f) x + deriv f x * deriv (deriv (deriv f)) x) := by
    have := ((hf.deriv'.hasDerivAt x).mul (hf.deriv'.deriv'.hasDerivAt x)).const_mul 2
    exact this.deriv
  show (Lebesgue.Lf (Ω.diff.ΓA f f) x - Ω.diff.ΓA f (Lebesgue.Lf f) x -
    Ω.diff.ΓA (Lebesgue.Lf f) f x) / 2 = _
  rw [e1, e2, e3]
  unfold Lebesgue.Lf
  rw [h1, h2]; ring

/-- The curvature-dimension inequality for `Ω.diff`, in the shape of `FullTriple.CD` (unavailable: no `FullTriple`
over `Ω.diff`, `BddOpen.no_fullTriple`); pointwise on `C^∞`. -/
def GenCD (ρ : ℝ) (n : ℝ≥0∞) : Prop :=
  1 ≤ n ∧ ∀ f : ℝ → ℝ, Lebesgue.Sm f → ∀ x : ℝ,
    ρ * Ω.diff.ΓA f f x + (n⁻¹).toReal * (Ω.diff.L f x) ^ 2 ≤ Ω.diff.Γ₂ f f x

/-- **G2**: `CD(ρ, n)` holds for every `ρ ≤ 0` and every `n ∈ [1, ∞]`. -/
theorem diff_CD {ρ : ℝ} {n : ℝ≥0∞} (hρ : ρ ≤ 0) (hn : 1 ≤ n) : Ω.GenCD ρ n := by
  refine ⟨hn, fun f hf x => ?_⟩
  rw [Ω.Γ₂_eq hf, Ω.ΓA_eq hf hf]
  have h1 : (n⁻¹).toReal ≤ 1 := by
    have : n⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hn
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  have h0 : 0 ≤ (n⁻¹).toReal := ENNReal.toReal_nonneg
  have hL : Ω.diff.L f x = deriv (deriv f) x := rfl
  rw [hL]
  nlinarith [mul_self_nonneg (deriv f x), mul_self_nonneg (deriv (deriv f) x),
    mul_nonneg h0 (sq_nonneg (deriv (deriv f) x)),
    mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (deriv (deriv f) x)),
    mul_nonneg (neg_nonneg.2 hρ) (mul_self_nonneg (deriv f x))]

end BddOpen

end MarkovTriple.BGL.Instances.IntervalGen
