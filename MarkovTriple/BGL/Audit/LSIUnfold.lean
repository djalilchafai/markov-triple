import MarkovTriple.BGL.Instances.OU.LSIMain

/-! Round-9 audit: unfold `ouFull_LS` to a concrete statement, (the old-surface `ou_lsi` equivalence was dropped with the legacy surface, DECISIONS 17).
NOT imported by the root. -/
open MeasureTheory ProbabilityTheory

namespace MarkovTriple.BGL.Audit.LSIUnfold

local notation "G" => gaussianReal 0 1

/-- Concrete Gaussian LSI, no framework structures visible. -/
theorem concrete_lsi (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) G ∧
    ((∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂G) -
        (∫ x, f x ^ 2 ∂G) * Real.log (∫ x, f x ^ 2 ∂G)
      ≤ 2 * ∫ x, (deriv f x) ^ 2 ∂G) := by
  have hfc : Continuous f := hf.continuous
  have hcs : HasCompactSupport (fun x => f x ^ 2 * Real.log (f x ^ 2)) := by
    refine HasCompactSupport.intro hc.isCompact (fun x hx => ?_)
    have : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [this]
  have hcont : Continuous (fun x => f x ^ 2 * Real.log (f x ^ 2)) :=
    Real.continuous_mul_log.comp (hfc.pow 2)
  refine ⟨hcont.integrable_of_hasCompactSupport hcs, ?_⟩
  have h := MarkovTriple.BGL.Instances.OU.ouFull_LS
  have hmem : f ∈ MarkovTriple.BGL.Instances.OU.ouFull.toDiffusionTriple.A₀ := ⟨hf, hc⟩
  have h2 := h.2.2.2 f hmem
  have hE : MarkovTriple.BGL.energy MarkovTriple.BGL.Instances.OU.ouFull.toDiffusionTriple.μ MarkovTriple.BGL.Instances.OU.ouFull.toDiffusionTriple.Γ f =
      ∫ x, (deriv f x) ^ 2 ∂G := by
    show ∫ x, deriv f x * deriv f x ∂G = _
    simp [sq]
  rw [hE] at h2
  change (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂G) - (∫ x, f x ^ 2 ∂G) * Real.log (∫ x, f x ^ 2 ∂G)
    ≤ 2 * 1 * (∫ x, (deriv f x) ^ 2 ∂G) + 0 * ∫ x, f x ^ 2 ∂G at h2
  linarith

#print axioms concrete_lsi

end MarkovTriple.BGL.Audit.LSIUnfold
