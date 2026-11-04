import Mathlib
import MarkovTriple.Stochastic.R25.Feller
import MarkovTriple.Stochastic.R24.Bridge

/-!
# Round 25 (E), part 3: the Feller kernels of `(ℝ^d, Lebesgue)` are the Gaussian heat kernels

`fellerKernelInf (lebesgueRd_isFellerC0 hd) t x = N(x, 2t I_d)` at every point (uniqueness of weakly continuous
representations), so `hM` of `fellerMarkovProcessBridgeInf` holds, exact Chapman-Kolmogorov, invariance of Lebesgue
measure, and a `MarkovProcessBridge` for Brownian motion on `ℝ^d` (with infinite invariant measure).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R25

open MarkovTriple.BGL MarkovTriple.BGL.LebesgueRd MarkovTriple.Stochastic MarkovTriple.Stochastic.R24

variable {d : ℕ}

/-- **Identification, at every point**: the exact Feller kernels of `(ℝ^d, Lebesgue)` are `N(x, 2t I_d)`. -/
theorem fellerKernelInf_lebesgueRd (hd : 1 ≤ d) (t : ℝ≥0) (x : Fin d → ℝ) :
    fellerKernelInf (lebesgueRd_isFellerC0 hd) t x = heatKernelRd d t x := by
  symm
  refine fellerKernelInf_unique (lebesgueRd_isFellerC0 hd) t (heatKernelRd d t) ?_ ?_ x
  · intro f
    have : (fun x => ∫ y, f y ∂(heatKernelRd d t x)) = heatRd (Real.sqrt (2 * t)) f := by
      funext x; exact integral_heatKernelRd t x f f.continuous
    rw [this]
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    exact continuous_heatRd f.continuous (fun x => by simpa using hC x) _
  · intro f u hu
    refine (lebesgueRd_semigroup_cc hd t f u hu).trans (Eventually.of_forall fun x => ?_)
    exact (integral_heatKernelRd t x f f.continuous).symm

theorem fellerKernelInf_lebesgueRd_kernel (hd : 1 ≤ d) (t : ℝ≥0) :
    fellerKernelInf (lebesgueRd_isFellerC0 hd) t = heatKernelRd d t :=
  Kernel.ext fun x => fellerKernelInf_lebesgueRd hd t x

/-- the hypothesis `hM` of `fellerMarkovProcessBridgeInf` holds: pointwise mass one -/
theorem lebesgueRd_hM (hd : 1 ≤ d) (t : ℝ≥0) (x : Fin d → ℝ) :
    fellerKernelInf (lebesgueRd_isFellerC0 hd) t x Set.univ = 1 := by
  rw [fellerKernelInf_lebesgueRd]; exact measure_univ

theorem heatKernelRd_zero : heatKernelRd d 0 = Kernel.id := by
  ext x : 1
  simp [heatKernelRd_apply, Measure.map_const, Kernel.id_apply]

/-- **Exact Chapman-Kolmogorov** for the heat kernels on `ℝ^d` (all `x`, all `s, t`). -/
theorem heatKernelRd_add (hd : 1 ≤ d) (s t : ℝ≥0) :
    heatKernelRd d (s + t) = heatKernelRd d t ∘ₖ heatKernelRd d s := by
  rw [← fellerKernelInf_lebesgueRd_kernel hd, ← fellerKernelInf_lebesgueRd_kernel hd,
    ← fellerKernelInf_lebesgueRd_kernel hd]
  exact fellerKernelInf_add _ s t

/-- **Invariance of Lebesgue measure**: `volume.bind κ_t = volume`. -/
theorem heatKernelRd_bind (hd : 1 ≤ d) (t : ℝ≥0) :
    (volume : Measure (Fin d → ℝ)).bind (heatKernelRd d t) = volume := by
  rw [← fellerKernelInf_lebesgueRd_kernel hd]
  exact fellerKernelInf_bind (lebesgueRd_isFellerC0 hd) (lebesgueRd_hM hd) t

/-- **Brownian motion on `ℝ^d` as a `MarkovProcessBridge`** (infinite invariant measure). -/
noncomputable def brownianBridgeRd (hd : 1 ≤ d) :
    MarkovProcessBridge (lebesgueRdFull d hd).toDiffusionTriple :=
  fellerMarkovProcessBridgeInf (lebesgueRd_isFellerC0 hd) (lebesgueRd_hM hd)

theorem brownianBridgeRd_kernel (hd : 1 ≤ d) : (brownianBridgeRd hd).kernel = heatKernelRd d := by
  funext t
  exact fellerKernelInf_lebesgueRd_kernel hd t

end MarkovTriple.Stochastic.R25
