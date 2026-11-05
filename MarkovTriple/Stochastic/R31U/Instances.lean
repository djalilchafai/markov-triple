import Mathlib
import MarkovTriple.Stochastic.R31U.Kernel
import MarkovTriple.Stochastic.R30T.Ellip

/-!
# Round 31 (U), part 6: the reduced bridges of R30T with (c) discharged (U4)

For `gibbsRdFull_unconditional` (`Hess V ≥ 0`), `fullU` (`Curv 0`) and `riemFull_unconditional` (`Curv 0`) the reference measure is a probability
measure with full support, so `rd_kernel_ac` applies: `κ_s(x,·) ≪ μ` for every `x`.  The ONLY remaining analytic hypothesis of the bridges is
`IsFellerC0` (decay at infinity; item (a)), which is NOT proved here.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R31U

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R27 MarkovTriple.Stochastic.R29 MarkovTriple.Stochastic.R30T

variable {d : ℕ}

section Gibbs

variable (G : GibbsRdData d)

theorem gibbsRdFull_kernel_ac (hV : HessGe G.V 0) (hF : IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple)
    (s : ℝ≥0) (hs : 0 < s) (x : Rd d) :
    fellerKernelInf hF s x ≪ G.gibbsRdFull_unconditional.toDiffusionTriple.μ := by
  have : IsProbabilityMeasure G.gibbsRdFull_unconditional.toDiffusionTriple.μ :=
    (inferInstance : IsProbabilityMeasure G.toEll.μ)
  exact rd_kernel_ac G.gibbsRdFull_unconditional rfl rfl (G.gibbsRdFull_CD_unconditional hV)
    (gibbsRdFull_hell G) hF s hs x

/-- R30T `gibbsRdFull_bridge_of_feller_ac` with (c) discharged: only `IsFellerC0` remains. -/
noncomputable def gibbsRdFull_bridge_of_feller_U (hV : HessGe G.V 0)
    (hF : IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple) :
    MarkovProcessBridge G.gibbsRdFull_unconditional.toDiffusionTriple :=
  gibbsRdFull_bridge_of_feller_ac G hV hF (fun s hs x => gibbsRdFull_kernel_ac G hV hF s hs x)

end Gibbs

section Ell

variable (E : EllData d) (R : Riemannian.RiemData d)

theorem fullU_kernel_ac (hC : E.Curv 0) (hF : IsFellerC0 E.fullU.toDiffusionTriple)
    (s : ℝ≥0) (hs : 0 < s) (x : Rd d) : fellerKernelInf hF s x ≪ E.fullU.toDiffusionTriple.μ := by
  have : IsProbabilityMeasure E.fullU.toDiffusionTriple.μ :=
    (inferInstance : IsProbabilityMeasure E.μ)
  exact rd_kernel_ac E.fullU rfl rfl (E.fullU_CD hC) (ellData_hell E) hF s hs x

noncomputable def fullU_bridge_of_feller_U (hC : E.Curv 0) (hF : IsFellerC0 E.fullU.toDiffusionTriple) :
    MarkovProcessBridge E.fullU.toDiffusionTriple :=
  fullU_bridge_of_feller_ac E hC hF (fun s hs x => fullU_kernel_ac E hC hF s hs x)

theorem riemFull_kernel_ac (hC : R.Curv 0) (hF : IsFellerC0 R.riemFull_unconditional.toDiffusionTriple)
    (s : ℝ≥0) (hs : 0 < s) (x : Rd d) :
    fellerKernelInf hF s x ≪ R.riemFull_unconditional.toDiffusionTriple.μ := by
  have : IsProbabilityMeasure R.riemFull_unconditional.toDiffusionTriple.μ :=
    (inferInstance : IsProbabilityMeasure R.toEll.μ)
  exact rd_kernel_ac R.riemFull_unconditional rfl rfl (R.riemFull_CD_unconditional hC)
    (ellData_hell R.toEll) hF s hs x

noncomputable def riemFull_bridge_of_feller_U (hC : R.Curv 0)
    (hF : IsFellerC0 R.riemFull_unconditional.toDiffusionTriple) :
    MarkovProcessBridge R.riemFull_unconditional.toDiffusionTriple :=
  riemFull_bridge_of_feller_ac R hC hF (fun s hs x => riemFull_kernel_ac R hC hF s hs x)

end Ell

end MarkovTriple.Stochastic.R31U
