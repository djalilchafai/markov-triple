import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Converse.Statements

/-!
# R24-B: converse of BGL Prop. 3.3.17 without completeness (finite dimension), and for `goFullTriple`

Statements: `STATEMENTS_R24_B.md`, `Statements.lean`.

## DIFFERENCE FROM BGL
BGL's converse is for `CD(ρ,∞)` and tacitly uses `Core2` (ERRATA R15-1); the Round 20 cut-off route uses completeness.  For
`CD(ρ,n)`, `n < ∞`, the dimensional term gives `(Lf)² ≤ n (Γ₂ f − ρ Γ f)` pointwise, hence `Lf ∈ L²` with no cut-offs;
F10 (ESA, a `FullTriple` field) and the maximal-domain lemma finish.  Hence completeness is not needed for `goFullTriple`.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

theorem memLp_L_of_Γ₂_finite (T : FullTriple E) : R24B_memLp_L T := by
  intro ρ n hn hCD f hf hG hG2
  have hmeas : Measurable (T.L f) := T.A_measurable _ (L_memA hf)
  have hn1 : (1 : ℝ≥0∞) ≤ n := hCD.1
  have hnr : 1 ≤ n.toReal := by
    have := (ENNReal.toReal_mono hn hn1)
    simpa using this
  have hinv : (n⁻¹).toReal = (n.toReal)⁻¹ := ENNReal.toReal_inv n
  have hpos : 0 < n.toReal := by linarith
  have hbd : ∀ᵐ x ∂T.μ, ‖T.L f x ^ 2‖ ≤ n.toReal * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) := by
    filter_upwards [hCD.2 f hf] with x hx
    rw [hinv] at hx
    have hx' : (n.toReal)⁻¹ * T.L f x ^ 2 ≤ T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x := by
      have : G T f f x = T.toDiffusionTriple.ΓA f f x := rfl
      rw [this]; linarith
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have := mul_le_mul_of_nonneg_left hx' hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
  have hint : Integrable (fun x => n.toReal * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x)) T.μ :=
    (hG2.sub (hG.const_mul ρ)).const_mul _
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    (hint.mono' (hmeas.pow_const 2).aestronglyMeasurable hbd)

theorem mem_domain_of_Γ₂_finite (T : FullTriple E) : R24B_converse T := by
  intro ρ n hn hCD f hf hf2 hG hG2
  have hLf2 := memLp_L_of_Γ₂_finite T hn hCD hf hG hG2
  obtain ⟨hF, hFe⟩ := mem_domain_of_maximal hf hf2 hLf2
  refine ⟨hF, ?_⟩
  rw [hFe]
  exact hLf2.coeFn_toLp

end FullTriple

end MarkovTriple.BGL

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

/-- **R24-B**: the converse of BGL Prop. 3.3.17 holds for the non-complete `goFullTriple` (so no counterexample). -/
theorem goFullTriple_mem_domain_of_Γ₂ : R24B_go_statement := by
  intro f hf hf2 hG hG2
  exact FullTriple.mem_domain_of_Γ₂_finite goFullTriple (n := 4) (by simp) goFullTriple_CD hf hf2 hG hG2

end MarkovTriple.BGL.Instances.GegenbauerOpen
