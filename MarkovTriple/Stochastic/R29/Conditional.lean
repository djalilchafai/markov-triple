import Mathlib
import MarkovTriple.Stochastic.R27.Mass
import MarkovTriple.BGL.Instances.Gibbs.RegMain
import MarkovTriple.BGL.Instances.GibbsRd.Unconditional
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllMain
import MarkovTriple.BGL.Instances.Riemannian.Unconditional

/-!
# Round 29 (O), part 5: conditional `MarkovProcessBridge`s for the Gibbs and Riemannian/elliptic `FullTriple`s

For `G.gibbsFull_unconditional` (`ℝ`, `e^{-V}`), `G.gibbsRdFull_unconditional` (`ℝ^d`), `E.fullU` (`ℝ^d`, elliptic data) and
`R.riemFull_unconditional` (`ℝ^d`, Riemannian data) the topological hypotheses of the R24/R27 Feller theory hold UNCONDITIONALLY: the
reference measure is a probability measure (so finite on compacts) of full support (strictly positive continuous density; the library instances
`GibbsData.μ.IsOpenPosMeasure`, `EllData.μ.IsOpenPosMeasure`).  What is NOT available in the library, and therefore left as hypotheses here:

* (a) `IsFellerC0` (the `C_0`-Feller property: `P_t C_c ⊂ C_0`);  for non-Gaussian `V` / non-constant elliptic data there is no
  explicit kernel, no Mehler formula, and the generic route (smoothing + decay at infinity) is not formalised;
* (c) `hac`: `κ_s(x, ·) ≪ μ` for all `s > 0`, EVERY `x` (only `μ`-a.e. `x` is available from reversibility/`L²` representation);
* (d) `hinit`: `P_t f(x) → f(x)` as `t ↓ 0` at every `x` for `f ∈ C_c` (strong continuity gives this only in `L²`).
The theorems are the R27 theorem `fellerMarkovProcessBridgeInf_of_ac_init` instantiated; no new analysis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R29

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.Stochastic MarkovTriple.Stochastic.R24
  MarkovTriple.Stochastic.R27

section Gibbs1

variable (G : Gibbs.GibbsData)

instance gibbsFull_locFin : IsFiniteMeasureOnCompacts G.gibbsFull_unconditional.toDiffusionTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts G.μ)

instance gibbsFull_openPos : G.gibbsFull_unconditional.toDiffusionTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs G.μ.IsOpenPosMeasure

instance gibbsFull_locFin' : IsFiniteMeasureOnCompacts G.gibbsFull_unconditional.toStandardTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts G.μ)

instance gibbsFull_openPos' : G.gibbsFull_unconditional.toStandardTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs G.μ.IsOpenPosMeasure

/-- **Conditional bridge for the 1-d Gibbs `FullTriple`** (hypotheses (a), (c), (d) above). -/
noncomputable def gibbsFull_bridge_of_feller (hF : IsFellerC0 G.gibbsFull_unconditional.toDiffusionTriple)
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ G.gibbsFull_unconditional.μ)
    (hinit : ∀ (x : ℝ) (f : C_c(ℝ, ℝ)),
      Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x))) :
    MarkovProcessBridge G.gibbsFull_unconditional.toDiffusionTriple :=
  fellerMarkovProcessBridgeInf_of_ac_init G.gibbsFull_unconditional.toStandardTriple hF hac hinit

end Gibbs1

section GibbsRd

variable {d : ℕ} (G : GibbsRd.GibbsRdData d)

instance gibbsRdFull_locFin : IsFiniteMeasureOnCompacts G.gibbsRdFull_unconditional.toDiffusionTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts G.toEll.μ)

instance gibbsRdFull_openPos : G.gibbsRdFull_unconditional.toDiffusionTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs G.toEll.μ.IsOpenPosMeasure

instance gibbsRdFull_locFin' : IsFiniteMeasureOnCompacts G.gibbsRdFull_unconditional.toStandardTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts G.toEll.μ)

instance gibbsRdFull_openPos' : G.gibbsRdFull_unconditional.toStandardTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs G.toEll.μ.IsOpenPosMeasure

/-- **Conditional bridge for the `ℝ^d` Gibbs `FullTriple`.** -/
noncomputable def gibbsRdFull_bridge_of_feller (hF : IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple)
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ G.gibbsRdFull_unconditional.μ)
    (hinit : ∀ (x : Fin d → ℝ) (f : C_c(Fin d → ℝ, ℝ)),
      Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x))) :
    MarkovProcessBridge G.gibbsRdFull_unconditional.toDiffusionTriple :=
  fellerMarkovProcessBridgeInf_of_ac_init G.gibbsRdFull_unconditional.toStandardTriple hF hac hinit

end GibbsRd

section Ell

variable {d : ℕ} (E : GibbsRd.EllData d)

instance fullU_locFin : IsFiniteMeasureOnCompacts E.fullU.toDiffusionTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts E.μ)

instance fullU_openPos : E.fullU.toDiffusionTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs E.μ.IsOpenPosMeasure

instance fullU_locFin' : IsFiniteMeasureOnCompacts E.fullU.toStandardTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts E.μ)

instance fullU_openPos' : E.fullU.toStandardTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs E.μ.IsOpenPosMeasure

/-- **Conditional bridge for the elliptic `FullTriple` `E.fullU`.** -/
noncomputable def fullU_bridge_of_feller (hF : IsFellerC0 E.fullU.toDiffusionTriple)
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ E.fullU.μ)
    (hinit : ∀ (x : Fin d → ℝ) (f : C_c(Fin d → ℝ, ℝ)),
      Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x))) :
    MarkovProcessBridge E.fullU.toDiffusionTriple :=
  fellerMarkovProcessBridgeInf_of_ac_init E.fullU.toStandardTriple hF hac hinit

end Ell

section Riem

variable {d : ℕ} (R : Riemannian.RiemData d)

instance riemFull_locFin : IsFiniteMeasureOnCompacts R.riemFull_unconditional.toDiffusionTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts R.toEll.μ)

instance riemFull_openPos : R.riemFull_unconditional.toDiffusionTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs R.toEll.μ.IsOpenPosMeasure

instance riemFull_locFin' : IsFiniteMeasureOnCompacts R.riemFull_unconditional.toStandardTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts R.toEll.μ)

instance riemFull_openPos' : R.riemFull_unconditional.toStandardTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs R.toEll.μ.IsOpenPosMeasure

/-- **Conditional bridge for the Riemannian `FullTriple`.** -/
noncomputable def riemFull_bridge_of_feller (hF : IsFellerC0 R.riemFull_unconditional.toDiffusionTriple)
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ R.riemFull_unconditional.μ)
    (hinit : ∀ (x : Fin d → ℝ) (f : C_c(Fin d → ℝ, ℝ)),
      Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x))) :
    MarkovProcessBridge R.riemFull_unconditional.toDiffusionTriple :=
  fellerMarkovProcessBridgeInf_of_ac_init R.riemFull_unconditional.toStandardTriple hF hac hinit

end Riem

end MarkovTriple.Stochastic.R29
