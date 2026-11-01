import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Basic
import MarkovTriple.BGL.Frozen.GammaA
import MarkovTriple.BGL.Frozen.Gamma2

/-!
# The Brownian triple on `(ℝ, Lebesgue)` as a `DiffusionTriple` (D1–D8)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

lemma tendsto_cs {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    Tendsto f atBot (𝓝 0) ∧ Tendsto f atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hf.isCompact.bddAbove
  obtain ⟨b, hb⟩ := hf.isCompact.bddBelow
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot b] with x hx
    exact (image_eq_zero_of_notMem_tsupport (fun h => absurd (hb h) (not_le.2 hx))).symm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop B] with x hx
    exact (image_eq_zero_of_notMem_tsupport (fun h => absurd (hB h) (not_le.2 hx))).symm

lemma integral_Lf {f : ℝ → ℝ} (hf : f ∈ A₀) : ∫ x, Lf f x = 0 := by
  have hd := deriv_mem hf
  have h := integral_of_hasDerivAt_of_tendsto (f := deriv f) (f' := deriv (deriv f))
    (m := 0) (n := 0) (fun x => (smooth hd).hasDerivAt x) (integrable_of (deriv_mem hd))
    (tendsto_cs (cs hd)).1 (tendsto_cs (cs hd)).2
  simpa [Lf] using h

/-- the exhaustion sequence of cutoffs. -/
lemma cut_exhaustion : MarkovTriple.BGL.IsExhaustion (volume : Measure ℝ) A₀ cut :=
  ⟨cut_mem, fun n => Filter.Eventually.of_forall (cut_mono n),
    Filter.Eventually.of_forall cut_tendsto⟩

lemma not_isFiniteMeasure : ¬ IsFiniteMeasure (volume : Measure ℝ) := fun h => by
  have := h.measure_univ_lt_top
  rw [Real.volume_univ] at this
  exact lt_irrefl _ this

/-- **The Brownian triple on `(ℝ, Lebesgue)`**: `𝒜₀ = C_c^∞(ℝ)`, `L f = f''`, `Γ(f,g) = f' g'`. -/
@[reducible] noncomputable def lebesgueDiffusion : MarkovTriple.BGL.DiffusionTriple ℝ where
  μ := volume
  sigmaFinite := inferInstance
  finite_prob := fun h => absurd h not_isFiniteMeasure
  A₀ := A₀
  measurable := fun f hf => (smooth hf).continuous.measurable
  bounded := fun f hf => by
    obtain ⟨C, hC⟩ := (smooth hf).continuous.bounded_above_of_compact_support (cs hf)
    exact ⟨C, fun x => by simpa using hC x⟩
  memLp := fun f hf p _ _ => memLp_of hf p
  dense := fun p hp hp' => by
    have := hp
    exact dense_Lp p hp'
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_A₀ k ψ hψ h0 f hf
  exhaustion := ⟨cut, cut_exhaustion⟩
  Γ := Gf
  L := Lf
  Γ_mem := fun f hf g hg => mul_mem (deriv_mem hf) (deriv_mem hg)
  L_mem := fun f hf => deriv_mem (deriv_mem hf)
  Γ_symm := fun f _ g _ => Filter.Eventually.of_forall fun x => by simp [Gf, mul_comm]
  Γ_add := fun f hf f' hf' g _ => Filter.Eventually.of_forall fun x => by
    simp [Gf, deriv_add_sm (smooth hf) (smooth hf'), add_mul]
  Γ_smul := fun c f hf g _ => Filter.Eventually.of_forall fun x => by
    simp [Gf, deriv_smul_sm c (smooth hf), mul_assoc]
  Γ_nonneg := fun f _ => Filter.Eventually.of_forall fun x => by
    simpa [Gf] using mul_self_nonneg (deriv f x)
  diffusion := fun k ψ hψ _ f hf g _ =>
    Filter.Eventually.of_forall fun x => by
      have := congrFun ((diffusion_c k ψ hψ f (fun i => smooth (hf i))).1 g) x
      simpa using this
  ibp := fun f hf g hg => ibp_L (smooth hf) hg
  integral_L := fun f hf => integral_Lf hf

end MarkovTriple.BGL.Lebesgue
