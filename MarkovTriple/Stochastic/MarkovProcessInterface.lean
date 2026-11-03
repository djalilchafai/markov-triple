import Mathlib
import MarkovTriple.Stochastic.Bridge
import MarkovTriple.Stochastic.OUFull
import MarkovTriple.Stochastic.Circle

/-!
# Stochastic layer, part 10: the `MarkovProcess` bridge as a precisely stated interface (no dependency)

Armstrong's library `MarkovProcess` (S. Armstrong, `scottnarmstrong/MarkovProcess`; DECISIONS 24: **not** a
dependency of this repository; it is not on the Lake search path and `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain` are untouched) defines
`MarkovProcess.SubMarkovKernelSemigroup α` as a structure with the five fields
```
kernel : NNReal → Kernel α α
measurable_kernel : Measurable fun p : NNReal × α ↦ kernel p.1 p.2
kernel_zero : kernel 0 = Kernel.id
kernel_add : ∀ s t, kernel (s + t) = (kernel t).comp (kernel s)
isSubMarkovKernel : ∀ t, IsSubMarkovKernel (kernel t)           -- IsSubMarkovKernel κ := ∀ x, κ x Set.univ ≤ 1
```
(file `MarkovProcess/Kernel/KernelSemigroup.lean`, read as plain text from an *untrusted* copy of the
repository found at `/tmp/lsi-armstrong-audit/sources/MarkovProcess` (a copy of unknown provenance (no .git directory; consistent with the upstream pin 666cda02 used by the sibling project SuperdiffusionCLT)); that copy is a
Lean-module-system project and is not importable here.)

This file records, **without any assumption and without `sorry`**, exactly what a bridge to that library
consists of on our side:

* `MarkovProcessSemigroupData E`: a field-by-field mirror of Armstrong's structure (the only difference is
  that `isSubMarkovKernel` is unfolded);
* `MarkovProcessBridge T`: that data together with the two properties required of a `KernelBridge`
  (`rep` on bounded measurable `L²` functions, and invariance of `T.μ`);
* `MarkovProcessBridge.toKernelBridge` / `KernelBridge.toMarkovProcessBridge`: the implication in both
  directions (the only extra input in the second direction is the joint measurability, which our
  `SubMarkovKernelSemigroup` does not require);
* instances: `ouMarkovProcessBridge`, `circleMarkovProcessBridge`, i.e. the data a `MarkovProcess` instance
  would be built from (jointly measurable, exact Chapman-Kolmogorov, `κ_0 = id`).

**What is blocked on the external library**: the identification of `MarkovProcessSemigroupData E` with
`MarkovProcess.SubMarkovKernelSemigroup E` (an equivalence of structures that is immediate field by field but
cannot be stated in a file that does not import `MarkovProcess`), and everything built on it (Feller property,
Dynkin formula, path-space processes).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- Field-by-field mirror of `MarkovProcess.SubMarkovKernelSemigroup E` (Armstrong). -/
structure MarkovProcessSemigroupData (E : Type*) [MeasurableSpace E] where
  /-- the transition kernel at a nonnegative time -/
  kernel : ℝ≥0 → Kernel E E
  /-- joint measurability in time and starting point -/
  measurable_kernel : Measurable fun p : ℝ≥0 × E => kernel p.1 p.2
  /-- at time zero the kernel is the identity kernel -/
  kernel_zero : kernel 0 = Kernel.id
  /-- Chapman-Kolmogorov, `K (s + t) = (K t).comp (K s)` -/
  kernel_add : ∀ s t, kernel (s + t) = (kernel t).comp (kernel s)
  /-- every transition measure has mass at most one (`IsSubMarkovKernel` unfolded) -/
  isSubMarkovKernel : ∀ t x, kernel t x Set.univ ≤ 1

/-- Forget joint measurability. -/
def MarkovProcessSemigroupData.toSubMarkovKernelSemigroup (D : MarkovProcessSemigroupData E) :
    SubMarkovKernelSemigroup E where
  κ := D.kernel
  subMarkov := D.isSubMarkovKernel
  zero := D.kernel_zero
  add := D.kernel_add

/-- Add joint measurability. -/
def SubMarkovKernelSemigroup.toMarkovProcessData (S : SubMarkovKernelSemigroup E)
    (hm : Measurable fun p : ℝ≥0 × E => S.κ p.1 p.2) : MarkovProcessSemigroupData E where
  kernel := S.κ
  measurable_kernel := hm
  kernel_zero := S.zero
  kernel_add := S.add
  isSubMarkovKernel := S.subMarkov

/-- The data a `MarkovProcess` bridge for the triple `T` would supply: a jointly measurable
sub-Markov transition semigroup (exact Chapman-Kolmogorov) which represents the `L²` semigroup of `T` on
bounded measurable `L²` functions and leaves `T.μ` invariant. -/
structure MarkovProcessBridge (T : DiffusionTriple E) extends MarkovProcessSemigroupData E where
  /-- the kernels realize `P_t` on bounded measurable `L²` functions -/
  rep : ∀ (t : ℝ≥0) (g : E → ℝ) (_hg : Measurable g) (_hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 T.μ),
    (T.semigroup t (hL.toLp g) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(kernel t x)
  /-- `T.μ` is invariant -/
  invariant : ∀ t, T.μ.bind (kernel t) = T.μ

/-- **The implication of the bridge**: a `MarkovProcessBridge` yields a `KernelBridge`
(hence a `KernelRepresentation`, a.e. Chapman-Kolmogorov, ...). -/
def MarkovProcessBridge.toKernelBridge {T : DiffusionTriple E} (B : MarkovProcessBridge T) :
    KernelBridge T where
  toSubMarkovKernelSemigroup := B.toMarkovProcessSemigroupData.toSubMarkovKernelSemigroup
  rep := B.rep
  invariant := B.invariant

/-- Converse: a `KernelBridge` with a jointly measurable kernel family is a `MarkovProcessBridge`. -/
def KernelBridge.toMarkovProcessBridge {T : DiffusionTriple E} (B : KernelBridge T)
    (hm : Measurable fun p : ℝ≥0 × E => B.κ p.1 p.2) : MarkovProcessBridge T where
  toMarkovProcessSemigroupData := B.toSubMarkovKernelSemigroup.toMarkovProcessData hm
  rep := B.rep
  invariant := B.invariant

/-- The two constructions are mutually inverse on the kernel family (definitional). -/
theorem KernelBridge.toMarkovProcessBridge_toKernelBridge_κ {T : DiffusionTriple E}
    (B : KernelBridge T) (hm : Measurable fun p : ℝ≥0 × E => B.κ p.1 p.2) :
    (B.toMarkovProcessBridge hm).toKernelBridge.κ = B.κ := rfl

/-- A jointly measurable family of `ℝ≥0`-parametrised Gaussian-type kernels:
if `(t, x) ↦ ν (t, x)` is measurable into `Measure ℝ`, the kernel `(t,x) ↦ ν(t,x).map φ` is jointly
measurable.  (helper for the instances below). -/
lemma measurable_family_of_measurable_map {F : Type*} [MeasurableSpace F] {Y : Type*}
    [MeasurableSpace Y] (ν : F → Measure ℝ) (hν : Measurable ν)
    (hprob : ∀ a, IsProbabilityMeasure (ν a)) (φ : F → ℝ → Y)
    (hφ : Measurable fun p : F × ℝ => φ p.1 p.2) :
    Measurable fun a : F => (ν a).map (φ a) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hmap : ∀ a : F, (ν a).map (φ a) A = ν a (Prod.mk a ⁻¹' ((fun p : F × ℝ => φ p.1 p.2) ⁻¹' A)) := by
    intro a
    rw [Measure.map_apply (by exact hφ.comp measurable_prodMk_left) hA]
    rfl
  simp_rw [hmap]
  let κ : Kernel F ℝ := ⟨ν, hν⟩
  have : IsMarkovKernel κ := ⟨hprob⟩
  exact Kernel.measurable_kernel_prodMk_left (κ := κ) (hφ hA)

/-! ### Instances: OU and circle supply the data -/

open MarkovTriple.Stochastic.OU in
/-- The OU Mehler kernels are jointly measurable in `(t, x)`. -/
theorem ouKernel_measurable_joint : Measurable fun p : ℝ≥0 × ℝ => ouKernel p.1 p.2 := by
  have hvar : Measurable ouVar := by
    have : ouVar = fun t : ℝ≥0 => (1 - Real.exp (-2 * (t : ℝ))).toNNReal := by
      funext t
      apply NNReal.eq
      rw [coe_ouVar, Real.coe_toNNReal _ (by rw [← coe_ouVar]; exact NNReal.coe_nonneg _)]
    rw [this]
    exact measurable_real_toNNReal.comp (by fun_prop)
  have hA : Measurable ouA := by unfold ouA; fun_prop
  have : Measurable fun p : ℝ≥0 × ℝ => ((ouA p.1 * p.2, ouVar p.1) : ℝ × ℝ≥0) := by
    have h1 : Measurable fun p : ℝ≥0 × ℝ => ouA p.1 * p.2 := (hA.comp measurable_fst).mul measurable_snd
    exact h1.prodMk (hvar.comp measurable_fst)
  exact measurable_gaussianReal.comp this

open MarkovTriple.Stochastic.OU in
/-- **The OU data of a `MarkovProcess` bridge.** -/
noncomputable def ouMarkovProcessBridge : MarkovProcessBridge MarkovTriple.BGL.Instances.OU.ouDiff :=
  ouKernelBridge.toMarkovProcessBridge ouKernel_measurable_joint

/-- The circle heat kernels are jointly measurable in `(t, x)`. -/
theorem circleKernel_measurable_joint :
    Measurable fun p : ℝ≥0 × MarkovTriple.Sanity.Circle.𝕋 => Circle.circleKernel p.1 p.2 := by
  have hν : Measurable fun a : ℝ≥0 × MarkovTriple.Sanity.Circle.𝕋 => Circle.heatGauss a.1 :=
    measurable_gaussianReal.comp (show Measurable fun a : ℝ≥0 × MarkovTriple.Sanity.Circle.𝕋 =>
      ((0 : ℝ), (2 * a.1 : ℝ≥0)) by fun_prop)
  exact measurable_family_of_measurable_map (fun a : ℝ≥0 × MarkovTriple.Sanity.Circle.𝕋 => Circle.heatGauss a.1) hν
    (fun a => inferInstance) (fun (a : ℝ≥0 × MarkovTriple.Sanity.Circle.𝕋) (z : ℝ) => a.2 + (z : MarkovTriple.Sanity.Circle.𝕋))
    ((measurable_snd.comp measurable_fst).add (Circle.measurable_coe𝕋.comp measurable_snd))

/-- **The circle data of a `MarkovProcess` bridge.** -/
noncomputable def circleMarkovProcessBridge : MarkovProcessBridge MarkovTriple.BGL.Circle.cT :=
  Circle.circleKernelBridge.toMarkovProcessBridge circleKernel_measurable_joint

end MarkovTriple.Stochastic
