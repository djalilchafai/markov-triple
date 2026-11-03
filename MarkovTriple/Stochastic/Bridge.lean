import Mathlib
import MarkovTriple.Stochastic.KernelRep

/-!
# Stochastic layer, part 3: the bridge interface

`SubMarkovKernelSemigroup E` is a minimal, Mathlib-only notion of a sub-Markov transition
semigroup `(κ_t)_{t ≥ 0}` of `ProbabilityTheory.Kernel E E` with *exact* Chapman–Kolmogorov
`κ_{s+t} = κ_t ∘ₖ κ_s` and `κ_0 = id`.  It is the shape an external development such as
Armstrong's `MarkovProcess` (`SubMarkovKernelSemigroup`, Feller processes, Dynkin's formula) would
be matched against; that library is **not** a dependency (an untrusted source copy exists on the filesystem but is never imported; see `MarkovProcessInterface.lean`).

`KernelBridge T` is the interface statement: a sub-Markov kernel semigroup that
(i) realizes the `L²` semigroup of the triple `T` on bounded measurable `L²` functions
(`rep`), and (ii) has `μ` as an invariant measure.  `KernelBridge.toKernelRepresentation` forgets
to the a.e.-Chapman–Kolmogorov interface of `KernelRep.lean`.
`IsTestClassRep` is the weaker (and in practice first available) form of `rep`, on the test
algebra `𝒜₀` only.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- A sub-Markov transition semigroup of kernels with exact Chapman–Kolmogorov. -/
structure SubMarkovKernelSemigroup (E : Type*) [MeasurableSpace E] where
  /-- the transition kernels -/
  κ : ℝ≥0 → Kernel E E
  /-- sub-probability -/
  subMarkov : ∀ t x, κ t x Set.univ ≤ 1
  /-- `κ_0 = id` -/
  zero : κ 0 = Kernel.id
  /-- Chapman–Kolmogorov, exactly: first run `s`, then `t` -/
  add : ∀ s t, κ (s + t) = κ t ∘ₖ κ s

/-- `μ` is invariant for the semigroup. -/
def SubMarkovKernelSemigroup.IsInvariant (S : SubMarkovKernelSemigroup E) (μ : Measure E) : Prop :=
  ∀ t, μ.bind (S.κ t) = μ

/-- The semigroup is conservative (Markov): every `κ_t(x, ·)` is a probability measure. -/
def SubMarkovKernelSemigroup.IsMarkov (S : SubMarkovKernelSemigroup E) : Prop :=
  ∀ t x, S.κ t x Set.univ = 1

/-- Representation of the `L²` semigroup by kernels on the test algebra `𝒜₀` only:
`P_t [f] = κ_t f` a.e. for every class with a representative `f ∈ 𝒜₀`. -/
def IsTestClassRep (T : DiffusionTriple E) (κ : ℝ≥0 → Kernel E E) : Prop :=
  ∀ (t : ℝ≥0) (f : E → ℝ), f ∈ T.A₀ → ∀ u : Lp ℝ 2 T.μ, (u : E → ℝ) =ᵐ[T.μ] f →
    (T.semigroup t u : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ t x)

/-- **The bridge interface.**  A kernel semigroup realizing the triple semigroup, with `μ`
invariant.  A `MarkovProcess` bridge instantiates this by producing its transition semigroup. -/
structure KernelBridge (T : DiffusionTriple E) extends SubMarkovKernelSemigroup E where
  /-- the kernels realize `P_t` on bounded measurable `L²` functions -/
  rep : ∀ (t : ℝ≥0) (g : E → ℝ) (_hg : Measurable g) (_hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 T.μ),
    (T.semigroup t (hL.toLp g) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(κ t x)
  /-- `μ` is invariant -/
  invariant : toSubMarkovKernelSemigroup.IsInvariant T.μ

/-- Forget to the a.e.-Chapman–Kolmogorov interface. -/
def KernelBridge.toKernelRepresentation {T : DiffusionTriple E} (B : KernelBridge T) :
    KernelRepresentation T where
  κ := B.κ
  subMarkov := B.subMarkov
  rep := B.rep

end MarkovTriple.Stochastic
