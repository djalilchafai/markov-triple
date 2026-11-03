import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Gibbs

/-!
# `BddHess3`: the hypothesis of the `ℝ^d` `Core2` theorem (R18, Stream A3)

Statements: `STATEMENTS_R18_Core2Rd.md` (B0).  `Hess V` and `∇³V` bounded; `∇V` is NOT assumed bounded (it grows at most
linearly, `BddHess3.grad_growth`, proved in `Core2RdCut.lean`), so `Hess V ≥ ρ > 0` is compatible with it.
-/

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- **B0**: bounded second and third derivatives of the potential. -/
structure GibbsRdData.BddHess3 (G : GibbsRdData d) : Prop where
  hess : ∃ C : ℝ, ∀ (x : Rd d) (i j : Fin d), |pderiv (pderiv G.V i) j x| ≤ C
  third : ∃ C : ℝ, ∀ (x : Rd d) (i j k : Fin d), |pderiv (pderiv (pderiv G.V i) j) k x| ≤ C

end MarkovTriple.BGL.Instances.GibbsRd
