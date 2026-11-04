import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.HypUnconditional
import MarkovTriple.BGL.Instances.Riemannian.Core2RiemMain
import MarkovTriple.BGL.Instances.Riemannian.R22.HypCutObstruction

/-!
# Round 24 (stream D), part C: what is available for the weighted hyperbolic plane (packaging only)

Everything needed by the BGL route `Curv ρ + CutFamily ⇒ Core2` except the cut-off family: `Curv 1`, `CD(1,∞)` hold, the
radial exhaustions `V`, `log(1+V)` do not satisfy `RadialJets` (R22-E4).  `Core2` for `hypRiem` itself is NOT claimed.
-/

open MarkovTriple.BGL.Instances.GibbsRd
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.Riemannian

/-- C1: curvature hypotheses available; the two radial cut-off exhaustions fail. -/
theorem hyp_core2_route_status :
    hypRiem.Curv 1 ∧ hypRiem.riemFull_unconditional.CD 1 ∞ ∧
    (∀ α β : ℝ → ℝ, ¬ RadialJets hypRiem.toEll Hyp.V α β) ∧
    (∀ α β : ℝ → ℝ, ¬ RadialJets hypRiem.toEll Hyp.psi α β) :=
  ⟨hypRiem.curv, hypRiem_CD, hypRiem.hyp_not_radialJets_V, hypRiem.hyp_not_radialJets_psi⟩

/-- C2: the conditional `Core2` theorem for `hypRiem`, whose only missing hypothesis is a cut-off family. -/
theorem hyp_core2_of_coreCut (h : hypRiem.toEll.CoreCut) : hypRiem.riemFull_unconditional.Core2 :=
  hypRiem.riem_core2 hypRiem.curv h

end MarkovTriple.BGL.Instances.Riemannian
