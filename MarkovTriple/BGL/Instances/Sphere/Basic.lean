import Mathlib
import MarkovTriple.BGL.Analysis.OU.Basic

/-!
# The zonal reduction of the round sphere `S³`: space, measure, test algebra

`S³ ⊂ ℝ⁴` with the normalised surface measure; for zonal functions `f(x₀)`, `x₀ = cos θ`, the
measure becomes `(2/π) sin²θ dθ` on `[0, π]`, i.e. `μ = (2/π) √(1-x²) dx` on `[-1, 1]`.  The space is
the compact interval `Zon = [-1,1]`.  The test algebra is
`𝒜 = {f : Zon → ℝ | θ ↦ f (cos θ) is `C^∞`}` (the zonal smooth functions of the sphere).
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.Sphere

/-- the zonal interval `[-1,1]` (compact). -/
abbrev Zon : Type := Set.Icc (-1 : ℝ) 1

/-- `θ ↦ cos θ ∈ [-1,1]`. -/
noncomputable def cosZ (θ : ℝ) : Zon := ⟨cos θ, neg_one_le_cos θ, cos_le_one θ⟩

lemma continuous_cosZ : Continuous cosZ := continuous_cos.subtype_mk _

/-- `x ↦ arccos x ∈ [0,π]`. -/
noncomputable def arc (x : Zon) : ℝ := arccos x.1

lemma continuous_arc : Continuous arc := continuous_arccos.comp continuous_subtype_val

lemma cosZ_arc (x : Zon) : cosZ (arc x) = x := Subtype.ext (cos_arccos x.2.1 x.2.2)

lemma arc_mem (x : Zon) : arc x ∈ Icc 0 π := ⟨arccos_nonneg _, arccos_le_pi _⟩

lemma arc_cosZ {θ : ℝ} (h : θ ∈ Icc 0 π) : arc (cosZ θ) = θ := arccos_cos h.1 h.2

/-- the lift of a function on `Zon` to the `θ`-line. -/
noncomputable def ext (f : Zon → ℝ) (θ : ℝ) : ℝ := f (cosZ θ)

/-- the function on `Zon` associated with a function of `θ`. -/
noncomputable def mk (H : ℝ → ℝ) (x : Zon) : ℝ := H (arc x)

lemma ext_neg (f : Zon → ℝ) (θ : ℝ) : ext f (-θ) = ext f θ := by
  simp [ext, cosZ]

lemma ext_add_two_pi (f : Zon → ℝ) (θ : ℝ) : ext f (θ + 2 * π) = ext f θ := by
  simp [ext, cosZ]

lemma mk_ext (f : Zon → ℝ) : mk (ext f) = f := funext fun x => by
  simp [mk, ext, cosZ_arc]

lemma ext_apply_of_mem (f : Zon → ℝ) {θ : ℝ} (h : θ ∈ Icc 0 π) : mk (ext f) (cosZ θ) = ext f θ := by
  simp [mk, ext, arc_cosZ h]

/-- an even `2π`-periodic function is invariant under `θ ↦ arccos (cos θ)`. -/
lemma arccos_cos_eq {H : ℝ → ℝ} (he : ∀ θ, H (-θ) = H θ) (hp : ∀ θ, H (θ + 2 * π) = H θ) (θ : ℝ) :
    H (arccos (cos θ)) = H θ := by
  have hc : cos (arccos (cos θ)) = cos θ := cos_arccos (neg_one_le_cos θ) (cos_le_one θ)
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.1 hc
  · have hper : Function.Periodic H (2 * π) := hp
    have : H θ = H (arccos (cos θ)) := by
      calc H θ = H (arccos (cos θ) + k * (2 * π)) := by congr 1; linear_combination hk
        _ = _ := hper.int_mul k _
    exact this.symm
  · have hper : Function.Periodic H (2 * π) := hp
    have : H θ = H (arccos (cos θ)) := by
      calc H θ = H (-arccos (cos θ) + k * (2 * π)) := by congr 1; linear_combination hk
        _ = H (-arccos (cos θ)) := hper.int_mul k _
        _ = _ := he _
    exact this.symm

lemma ext_mk {H : ℝ → ℝ} (he : ∀ θ, H (-θ) = H θ) (hp : ∀ θ, H (θ + 2 * π) = H θ) :
    ext (mk H) = H := funext fun θ => by
  simp only [ext, mk, arc, cosZ]
  exact arccos_cos_eq he hp θ

/-! ### the measure -/

/-- the density `(2/π) sin² θ` on `(0, π]`. -/
noncomputable def wθ (θ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (2 / π * sin θ ^ 2)

/-- the measure `(2/π) sin² θ dθ` on `(0,π]`, as a measure on `ℝ`. -/
noncomputable def ν : Measure ℝ := (volume.restrict (Ioc 0 π)).withDensity wθ

/-- the zonal measure on `[-1,1]`: image of `ν` under `cos`. -/
noncomputable def μZ : Measure Zon := ν.map cosZ

lemma measurable_wθ : Measurable wθ := by unfold wθ; fun_prop

lemma integral_ν (g : ℝ → ℝ) :
    ∫ θ, g θ ∂ν = ∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * g θ := by
  unfold ν
  rw [integral_withDensity_eq_integral_toReal_smul measurable_wθ
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), intervalIntegral.integral_of_le pi_pos.le]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [wθ, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]

instance : IsProbabilityMeasure ν := by
  refine ⟨?_⟩
  unfold ν
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : IntegrableOn (fun θ => 2 / π * sin θ ^ 2) (Ioc 0 π) volume :=
    (by fun_prop : Continuous fun θ : ℝ => 2 / π * sin θ ^ 2).integrableOn_Ioc
  have := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun θ => by positivity)
  unfold wθ
  rw [← this, ← intervalIntegral.integral_of_le pi_pos.le, intervalIntegral.integral_const_mul,
    integral_sin_sq]
  simp only [sin_zero, cos_zero, sin_pi, cos_pi]
  have : 2 / π * ((0 * 1 - 0 * -1 + π - 0) / 2) = 1 := by field_simp; ring
  rw [this]; simp

instance : IsProbabilityMeasure μZ := (Measure.isProbabilityMeasure_map_iff continuous_cosZ.aemeasurable).2 inferInstance

lemma integral_μZ {φ : Zon → ℝ} (hφ : Continuous φ) :
    ∫ x, φ x ∂μZ = ∫ θ in (0 : ℝ)..π, 2 / π * sin θ ^ 2 * φ (cosZ θ) := by
  unfold μZ
  rw [integral_map continuous_cosZ.aemeasurable hφ.aestronglyMeasurable, integral_ν]

/-! ### the test algebra -/

/-- `𝒜 = {f | θ ↦ f(cos θ) smooth}`, a unital subalgebra. -/
def AZ : Subalgebra ℝ (Zon → ℝ) where
  carrier := {f | Sm (ext f)}
  add_mem' := fun {f g} hf hg => by
    have : ext (f + g) = ext f + ext g := rfl
    show Sm (ext (f + g)); rw [this]; exact ContDiff.add hf hg
  mul_mem' := fun {f g} hf hg => by
    have : ext (f * g) = ext f * ext g := rfl
    show Sm (ext (f * g)); rw [this]; exact ContDiff.mul hf hg
  algebraMap_mem' := fun r => by
    show Sm (ext (algebraMap ℝ (Zon → ℝ) r))
    exact contDiff_const

lemma mem_AZ {f : Zon → ℝ} : f ∈ AZ ↔ Sm (ext f) := Iff.rfl

/-- the non-unital test algebra `𝒜₀ = 𝒜`. -/
def A0Z : NonUnitalSubalgebra ℝ (Zon → ℝ) := AZ.toNonUnitalSubalgebra

lemma mem_A0Z {f : Zon → ℝ} : f ∈ A0Z ↔ Sm (ext f) := Iff.rfl

lemma continuous_of_mem {f : Zon → ℝ} (hf : f ∈ AZ) : Continuous f := by
  have h : f = fun x => ext f (arc x) := by funext x; simp [ext, cosZ_arc]
  rw [h]
  exact (show Sm (ext f) from hf).continuous.comp continuous_arc

lemma mk_mem {H : ℝ → ℝ} (hH : Sm H) (he : ∀ θ, H (-θ) = H θ) (hp : ∀ θ, H (θ + 2 * π) = H θ) :
    mk H ∈ AZ := by
  show Sm (ext (mk H))
  rw [ext_mk he hp]; exact hH

lemma bounded_of_mem {f : Zon → ℝ} (hf : f ∈ AZ) : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set Zon)).exists_bound_of_continuousOn
    (continuous_of_mem hf).continuousOn
  exact ⟨C, fun x => by simpa using hC x (mem_univ x)⟩

lemma memLp_of_mem {f : Zon → ℝ} (hf : f ∈ AZ) (p : ℝ≥0∞) : MemLp f p μZ := by
  obtain ⟨C, hC⟩ := bounded_of_mem hf
  exact MemLp.of_bound (continuous_of_mem hf).aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa using hC x)

lemma integrable_of_cont {f : Zon → ℝ} (hf : Continuous f) : Integrable f μZ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- the subalgebra of `C(Zon, ℝ)` of zonal smooth functions. -/
def AC : Subalgebra ℝ C(Zon, ℝ) where
  carrier := {g | (g : Zon → ℝ) ∈ AZ}
  add_mem' := fun {f _g} hf hg => add_mem (show (f : Zon → ℝ) ∈ AZ from hf) hg
  mul_mem' := fun {f _g} hf hg => mul_mem (show (f : Zon → ℝ) ∈ AZ from hf) hg
  algebraMap_mem' := fun r => AZ.algebraMap_mem r

lemma AC_sep : AC.SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨⟨fun z : Zon => z.1, continuous_subtype_val⟩, ?_, rfl⟩, ?_⟩
  · show Sm (ext (fun z : Zon => z.1))
    exact (by simpa [ext, cosZ] using contDiff_cos : Sm fun θ => cos θ)
  · simpa using Subtype.val_injective.ne hxy

lemma AC_top : AC.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints AC AC_sep

lemma dense_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p μZ | ∃ f ∈ A0Z, (u : Zon → ℝ) =ᵐ[μZ] f} := by
  have h1 : DenseRange (ContinuousMap.toLp (E := ℝ) p μZ ℝ : C(Zon, ℝ) →L[ℝ] Lp ℝ p μZ) :=
    ContinuousMap.toLp_denseRange ℝ μZ ℝ hp
  have h2 : Dense (AC : Set C(Zon, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, AC_top]; rfl
  have h3 := h1.dense_image (ContinuousMap.toLp (E := ℝ) p μZ ℝ).continuous h2
  refine h3.mono ?_
  rintro _ ⟨F, hF, rfl⟩
  exact ⟨F, hF, ContinuousMap.coeFn_toLp _ _⟩

end MarkovTriple.BGL.Instances.Sphere
