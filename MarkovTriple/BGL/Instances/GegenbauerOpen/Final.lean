import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.Main
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Main

/-!
# Round 23: the first non-complete `FullTriple` with `CD`

Composition of stream G1 (`go_esaProp`: F10 for the zonal Gegenbauer triple `λ = 3/2`, i.e. `S⁴`
minus its two poles, with `𝒜₀ = C_c^∞((-1,1))`) and stream G2 (`goFull`: every `FullTriple` field
except F10 proved).  No new mathematics: this file only discharges the hypothesis `hF10`.

## DIFFERENCE FROM BGL
BGL's completeness (Def. 3.3.9) fails here (`goFull_not_complete`), while F1–F10 and `CD(3,4)` hold; so
`FullTriple.mem_domain_of_Γ₂_direct` (needs completeness) does not apply, and the Round 20 route to the
converse of Prop. 3.3.17 is not available for this triple.  See ERRATA R23-G1-*, R23-G2-*, R23-F-1.
-/

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open MarkovTriple.BGL

/-- The non-complete `FullTriple` on `(-1,1)` (zonal `S⁴` minus poles). -/
noncomputable def goFullTriple : FullTriple ℝ := goFull go_esaProp

/-- It satisfies `CD(3,4)` (the library's `FullTriple.CD`). -/
theorem goFullTriple_CD : goFullTriple.CD 3 4 := goFull_CD go_esaProp

/-- It is NOT complete in the sense of BGL Def. 3.3.9. -/
theorem goFullTriple_not_complete : ¬ goFullTriple.toDiffusionTriple.IsComplete :=
  goFull_not_complete go_esaProp

end MarkovTriple.BGL.Instances.GegenbauerOpen
