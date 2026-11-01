import Mathlib
import MarkovTriple.Divergences.Wasserstein

/-!
# Weak Kantorovich duality for `W₂²`

Ported from cutoff-rigidity-diffusions `TransportWeakDuality.lean` (`squaredWasserstein` is now
`wassersteinSq`).
-/

namespace MarkovTriple
open MeasureTheory
open scoped ENNReal

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- Actual integrable dual potentials give a lower bound for the genuine
primal quadratic coupling infimum, with infinite costs included. -/
theorem quadratic_transport_weak_duality
    (μ ν : Measure E) (f g : E → ℝ) (hf : Integrable f μ) (hg : Integrable g ν)
    (hdual : ∀ x y, f x + g y ≤ dist x y ^ 2) :
    ENNReal.ofReal ((∫ x, f x ∂μ) + ∫ y, g y ∂ν) ≤ wassersteinSq μ ν := by
  apply le_iInf
  intro π
  by_cases htop : (∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val) = ⊤
  · rw [htop]; exact le_top
  have hfMap : Integrable f (π.val.map Prod.fst) := by rwa [π.property.1]
  have hgMap : Integrable g (π.val.map Prod.snd) := by rwa [π.property.2]
  have hfπ := hfMap.comp_measurable measurable_fst
  have hgπ := hgMap.comp_measurable measurable_snd
  have hcost : Integrable (fun z : E×E => dist z.1 z.2 ^ 2) π.val := by
    refine ⟨by fun_prop, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
    have he : (∫⁻ z : E×E, ENNReal.ofReal ‖dist z.1 z.2 ^ 2‖ ∂π.val) =
        ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
      apply lintegral_congr
      intro z
      rw [Real.norm_of_nonneg (sq_nonneg _),edist_dist,
        ENNReal.ofReal_pow dist_nonneg 2]
    rw [he]
    exact lt_top_iff_ne_top.mpr htop
  have hi := integral_mono (hfπ.add hgπ) hcost (fun z : E×E => hdual z.1 z.2)
  simp only [Pi.add_def] at hi
  rw [integral_add hfπ hgπ] at hi
  have hF := integral_map measurable_fst.aemeasurable hfMap.aestronglyMeasurable
  have hG := integral_map measurable_snd.aemeasurable hgMap.aestronglyMeasurable
  rw [π.property.1] at hF
  rw [π.property.2] at hG
  change (∫ z, f z.1 ∂π.val) + (∫ z, g z.2 ∂π.val) ≤ _ at hi
  rw [← hF,← hG] at hi
  calc
    _ ≤ ENNReal.ofReal (∫ z : E×E, dist z.1 z.2 ^ 2 ∂π.val) := ENNReal.ofReal_le_ofReal hi
    _ = ∫⁻ z : E×E, ENNReal.ofReal (dist z.1 z.2 ^ 2) ∂π.val :=
      ofReal_integral_eq_lintegral_ofReal hcost (Filter.Eventually.of_forall fun z => sq_nonneg _)
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [edist_dist,ENNReal.ofReal_pow dist_nonneg 2]

/-- Normed-space form of weak duality, with the cost `‖x - y‖²`. -/
theorem quadratic_transport_weak_duality_norm {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ ν : Measure F) (f g : F → ℝ) (hf : Integrable f μ) (hg : Integrable g ν)
    (hdual : ∀ x y, f x + g y ≤ ‖x - y‖ ^ 2) :
    ENNReal.ofReal ((∫ x, f x ∂μ) + ∫ y, g y ∂ν) ≤ wassersteinSq μ ν :=
  quadratic_transport_weak_duality μ ν f g hf hg (by simpa [dist_eq_norm] using hdual)

end MarkovTriple
