import Mathlib
import MarkovTriple.Stochastic.FellerKernel
import MarkovTriple.BGL.Instances.Sphere.Semi

/-!
# Stochastic layer, part 18: the zonal sphere `S³` has an exact kernel semigroup (round 16, `STATEMENTS_R16.md` T4)

`Zon = [-1,1]` (compact), `μZ = (2/π) √(1-x²) dx`, `sT` the zonal `S³` triple.

* `μZ.IsOpenPosMeasure` (full support), proved by pulling back to `θ`-space (`μZ = (ν).map cos`,
  `ν = (2/π) sin² θ dθ` on `(0,π]`).
* `sphere_isFeller`: `P_t [f]` has a continuous representative for `f ∈ C(Zon)`: this is
  `Sphere.semigroup_cls_mem` (smoothing, `t > 0`; `t = 0` trivial) on the sup-norm dense subalgebra `AC`
  (`AC_top`, Stone-Weierstrass) plus the Feller criterion `isFeller_of_dense`.
* `sphereBridge : KernelBridge sT` from `semigroup_one` (conservativeness).

No heat-kernel formula is claimed: the kernels are the abstract Riesz-Markov kernels of `FellerKernel.lean`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Real


namespace MarkovTriple.Stochastic.Sphere

open MarkovTriple.BGL MarkovTriple.BGL.Instances.Sphere

instance : Measure.IsOpenPosMeasure μZ := ⟨fun U hU hne h0 => by
  obtain ⟨x, hx⟩ := hne
  set V : Set ℝ := cosZ ⁻¹' U with hV
  have hVo : IsOpen V := hU.preimage continuous_cosZ
  have hmap : μZ U = ν V := Measure.map_apply continuous_cosZ.measurable hU.measurableSet
  have hθ : arc x ∈ V := by
    show cosZ (arc x) ∈ U
    rw [cosZ_arc]; exact hx
  have hmem : arc x ∈ closure (Ioo (0 : ℝ) π) := by
    rw [closure_Ioo Real.pi_pos.ne]; exact arc_mem x
  obtain ⟨θ, hθV, hθI⟩ := mem_closure_iff.1 hmem V hVo hθ
  have hWo : IsOpen (V ∩ Ioo 0 π) := hVo.inter isOpen_Ioo
  have hWpos : 0 < volume (V ∩ Ioo 0 π) := hWo.measure_pos volume ⟨θ, hθV, hθI⟩
  have hν0 : ν V = 0 := hmap ▸ h0
  have hmeas : Measurable wθ := measurable_wθ
  have := (withDensity_apply_eq_zero' (μ := volume.restrict (Ioc 0 π)) hmeas.aemeasurable (s := V)).1 hν0
  have h1 : volume (V ∩ Ioo 0 π) = 0 := by
    refine measure_mono_null ?_ (by
      rwa [Measure.restrict_apply' measurableSet_Ioc] at this)
    intro θ hθ
    refine ⟨⟨?_, hθ.1⟩, Ioo_subset_Ioc_self hθ.2⟩
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.2.1 hθ.2.2
    show wθ θ ≠ 0
    unfold wθ
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  exact hWpos.ne' h1⟩

instance : IsFiniteMeasure sT.μ := inferInstanceAs (IsFiniteMeasure μZ)

instance : Measure.IsOpenPosMeasure sT.μ := inferInstanceAs (Measure.IsOpenPosMeasure μZ)

/-- **The zonal sphere is Feller.** -/
theorem sphere_isFeller : IsFeller sT := by
  refine isFeller_of_dense sT (D := (AC : Set C(Zon, ℝ))) ?_ ?_
  · rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, AC_top]; rfl
  · intro t d hd
    obtain ⟨g, hg, hae⟩ := semigroup_cls_mem t ⟨d, hd⟩
    refine ⟨⟨g, continuous_of_mem hg⟩, ?_⟩
    have e : clsC sT.μ d = sT.cls ⟨d, hd⟩ :=
      Lp.ext ((coeFn_clsC d).trans (DiffusionTriple.coeFn_cls sT ⟨d, hd⟩).symm)
    rw [e]
    exact hae

/-- **An exact `KernelBridge` for the zonal sphere `S³`** (Markov kernels, exact Chapman-Kolmogorov,
`κ_0 = id`, `μZ` invariant, representation of `P_t`). -/
noncomputable def sphereBridge : KernelBridge sT :=
  fellerBridge sphere_isFeller (fun t => semigroup_one t)

theorem sphereBridge_isMarkov : sphereBridge.toSubMarkovKernelSemigroup.IsMarkov :=
  fellerBridge_isMarkov sphere_isFeller _

end MarkovTriple.Stochastic.Sphere
