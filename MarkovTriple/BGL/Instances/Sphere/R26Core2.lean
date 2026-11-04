import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Compact
import MarkovTriple.BGL.Theory.Extension.R26.Core2Eigen

/-!
# Round 26 (stream I): `Core2` for the compact zonal sphere `S³`

`sFull_core2 : sFull.Core2` from the eigenbasis criterion `FullTriple.core2_of_eigen'` with the Chebyshev (second kind)
eigenfunctions `U_k`, `L U_k = -k(k+2) U_k`, whose classes span a dense subspace (`dense_span_eZ`).
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.Sphere

/-- **I3.**  `Core2` for the compact zonal sphere. -/
theorem sFull_core2 : sFull.Core2 := by
  refine FullTriple.core2_of_eigen' (T := sFull)
    (Set.range fun k : ℕ => (⟨UZ k, UZ_mem k⟩ : sFull.A₀)) ?_ ?_
  · rintro _ ⟨k, rfl⟩
    refine ⟨(k : ℝ) * (k + 2), by positivity, Filter.Eventually.of_forall fun x => ?_⟩
    show LZ (UZ k) x = _
    rw [LZ_UZ]
  · refine top_le_iff.1 ?_
    have hS : sFull.toDiffusionTriple.cls '' Set.range (fun k : ℕ => (⟨UZ k, UZ_mem k⟩ : sFull.A₀)) =
        Set.range eZ := by
      ext u
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩; exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩; exact ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [hS]
    exact dense_span_eZ

end MarkovTriple.BGL.Instances.Sphere
