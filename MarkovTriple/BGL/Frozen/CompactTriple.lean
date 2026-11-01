import Mathlib
import MarkovTriple.BGL.Frozen.FullTriple

/-! # Compact Markov Triples (BGL Definition 3.3.26) -/

namespace MarkovTriple.BGL

/-- A **Compact Markov Triple** (BGL Def. 3.3.26, §3.4.4): a Full Markov Triple with `𝒜 = 𝒜₀`.
(The ESA field is then automatic, a theorem to be proved; it is not removed from the structure.) -/
structure CompactTriple (E : Type*) [MeasurableSpace E] extends FullTriple E where
  /-- `𝒜 = 𝒜₀`. -/
  A_eq : ∀ f, f ∈ A ↔ f ∈ A₀

end MarkovTriple.BGL
