import Mathlib
import MarkovTriple.BGL.Frozen.FullTriple

/-! # Compact Markov Triples (BGL Definition 3.3.26) -/

namespace MarkovTriple.BGL

/-- A **Compact Markov Triple** (BGL Def. 3.3.26, §3.4.4): a Full Markov Triple with `𝒜 = 𝒜₀`.
(The ESA field is then automatic, a theorem to be proved; it is not removed from the structure.)
Since `𝒜` is a unital `Subalgebra` and `𝒜 = 𝒜₀`, the constant `1` lies in `𝒜₀ ⊂ L¹(μ)`; hence `μ` is
finite (so a probability measure by `finite_prob`) and `𝒜₀` is unital.  This is exactly the book's
compact case (compact manifolds); it is stated here rather than as a field (audit R2/L4).  "Compact" is
the frozen sense `𝒜 = 𝒜₀`, not topological compactness of the underlying space. -/
structure CompactTriple (E : Type*) [MeasurableSpace E] extends FullTriple E where
  /-- `𝒜 = 𝒜₀`. -/
  A_eq : ∀ f, f ∈ A ↔ f ∈ A₀

end MarkovTriple.BGL
