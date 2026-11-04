import Mathlib
import MarkovTriple.Stochastic.R24.Compact
import MarkovTriple.Stochastic.R24.Bridge
import MarkovTriple.Stochastic.CircleFeller
import MarkovTriple.Stochastic.SphereFeller

/-!
# Round 24 (C), part 9: non-vacuity of `IsFellerC0` and compatibility with the compact (R16/R17) Feller kernels

* `isFellerC0_of_isFeller`: on a compact space, `IsFeller T` (R16) implies `IsFellerC0 T`;
* `fellerKernelInf_eq_fellerKernel`: the new kernels coincide with the R16 `fellerKernel` at every point
  (uniqueness of weakly continuous representations);
* `circle_isFellerC0`, `sphere_isFellerC0`: the circle and the zonal `S³` heat semigroups are `C_0`-Feller, so the
  exact CK / bridge statements of R24 apply to them (and agree with `circleKernel`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.Stochastic

section CompactInst

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {T : DiffusionTriple X} [IsFiniteMeasure T.μ]
  [T.μ.IsOpenPosMeasure]

omit [T2Space X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] in
/-- On a compact space the Feller property of R16 gives the `C_0`-Feller property. -/
theorem isFellerC0_of_isFeller (hF : IsFeller T) : IsFellerC0 T := by
  intro t f u hu
  have e : u = clsC T.μ f.toContinuousMap :=
    Lp.ext (hu.trans (coeFn_clsC (μ := T.μ) f.toContinuousMap).symm)
  obtain ⟨g, hg⟩ := hF t f.toContinuousMap
  refine ⟨⟨g, ?_⟩, ?_⟩
  · rw [cocompact_eq_bot]; exact tendsto_bot
  · rw [e]; exact hg

/-- The `R24` kernels coincide with the compact Feller kernels of R16 at every point. -/
theorem fellerKernelInf_eq_fellerKernel (hF : IsFeller T) (t : ℝ≥0) (x : X) :
    fellerKernelInf (isFellerC0_of_isFeller hF) t x = fellerKernel hF t x := by
  have fin : ∀ y, IsFiniteMeasure (fellerKernelInf (isFellerC0_of_isFeller hF) t y) :=
    fun y => inferInstance
  refine fellerKernel_unique hF t (fellerKernelInf (isFellerC0_of_isFeller hF) t) ?_ ?_ x
  · intro f
    let f' : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
    have : (fun x => ∫ y, f y ∂(fellerKernelInf (isFellerC0_of_isFeller hF) t x))
        = ⇑(Qop (isFellerC0_of_isFeller hF) t f') := by
      funext x; exact integral_fellerKernelInf (isFellerC0_of_isFeller hF) t x f'
    rw [this]; exact (Qop _ t f').continuous
  · intro f
    let f' : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
    obtain ⟨g, hg, hae⟩ := fellerKernelInf_integral_cc (isFellerC0_of_isFeller hF) t f' (clsC T.μ f)
      (coeFn_clsC (μ := T.μ) f)
    exact hae.trans (Filter.Eventually.of_forall fun x => hg x)

end CompactInst

section Examples

/-- The circle heat semigroup is `C_0`-Feller. -/
theorem circle_isFellerC0 : IsFellerC0 MarkovTriple.BGL.Circle.cT :=
  isFellerC0_of_isFeller Circle.circle_isFeller

/-- the R24 kernels of the circle are the wrapped Gaussian kernels, at every point -/
theorem circle_fellerKernelInf_eq (t : ℝ≥0) :
    fellerKernelInf circle_isFellerC0 t = Circle.circleKernel t := by
  ext x : 1
  rw [fellerKernelInf_eq_fellerKernel Circle.circle_isFeller t x, Circle.circle_fellerKernel_eq']

/-- The zonal `S³` heat semigroup is `C_0`-Feller. -/
theorem sphere_isFellerC0 : IsFellerC0 MarkovTriple.BGL.Instances.Sphere.sT :=
  isFellerC0_of_isFeller Sphere.sphere_isFeller

end Examples

end MarkovTriple.Stochastic.R24
