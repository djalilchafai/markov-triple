import Mathlib
import MarkovTriple.BGL.Theory.Interp.EntropyFisher
import MarkovTriple.BGL.Theory.Interp.EntropyIdentity

/-!
# `EntropyInterpolation` for every `FullTriple` of finite measure with `CD(ρ,n)`, `ρ ≥ 0` (BGL Prop. 5.5.3, 5.7.1)

`FullTriple.entropyInterpolation : T.CD ρ n → 0 ≤ ρ → [IsFiniteMeasure T.μ] → T.EntropyInterpolation`.

The four fields of the frozen structure (G3 of `Theory/GAPS.md`) are:
continuity of `e`, `I` (`EntropyDeBruijn`), `e' = -I` (`EntropyDeBruijn`), and `I' = -2J` with the integrability of
`g Γ₂(Λ∘g)`, `g Γ(Λ∘g)` (`EntropyFisher` for the derivative of `I = -∫ Λ(g) L g`, `EntropyIdentity` for the
identification with `J`).  Standing hypotheses: finite `μ` (otherwise `entE` is junk), `ρ ≥ 0` (for the bound
`Γ(P_t φ) ≤ B`, Thm 3.3.18).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E} [IsFiniteMeasure T.μ]

/-- the regularity facts about `P = P_s φ` required by `fisher_alg`. -/
theorem fisherHyp {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ) (φ : T.A₀) {M : ℝ} (hM : 0 < M)
    (h0 : 0 ≤ᵐ[T.μ] φ.1) (hφ : ∀ x, φ.1 x ≤ M) (s : ℝ) :
    ∃ B : ℝ, FisherHyp T (T.Pt s.toNNReal φ) M B := by
  obtain ⟨B1, hB1, hΓ⟩ := Γ_Pt_bdd hCD hρ φ
  obtain ⟨c, hc, hb⟩ := orb_bdd (T := T) (T.Lt φ)
  have hP := T.Pt_mem_A s.toNNReal φ
  have hP2 := T.Pt_memLp s.toNNReal φ
  have hQ : T.L (T.Pt s.toNNReal φ) =ᵐ[T.μ] (T.Pt s.toNNReal (T.Lt φ)) :=
    (L_Pt_ae φ s).trans (T.orb_ae (T.Lt φ) s)
  have hQA : T.L (T.Pt s.toNNReal φ) ∈ T.A := L_memA hP
  have hQ' : T.Pt s.toNNReal (T.Lt φ) ∈ T.A := T.Pt_mem_A _ _
  refine ⟨max c B1, ⟨le_max_of_le_right hB1, hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · filter_upwards [T.Pt_nonneg s.toNNReal φ h0, Pt_le T φ hM hφ s.toNNReal] with x h1 h2
    exact ⟨h1, h2⟩
  · filter_upwards [hΓ s.toNNReal] with x hx
    exact hx.trans (le_max_right _ _)
  · filter_upwards [hQ, hb s, T.orb_ae (T.Lt φ) s] with x h1 h2 h3
    rw [h1]
    have : |(T.orb (T.Lt φ) s : E → ℝ) x| ≤ c := h2
    rw [h3] at this
    exact this.trans (le_max_left _ _)
  · exact integrable_Γ_Pt φ s
  · -- Γ(L P) = Γ(P_s Lφ) a.e.
    refine (integrable_Γ_Pt (T.Lt φ) s).congr ?_
    exact (T.ΓA_congr_A hQ' hQA hQ.symm)
  · exact ((memLp_L_Pt (T.Lt φ) s).integrable one_le_two).congr (L_congr_A T hQA hQ' hQ).symm
  · obtain ⟨-, hΓ₂, -⟩ := integrable_Γ₂_of_domain hCD hP hP2 (Pt_mem_dom φ s)
    exact hΓ₂

/-- **`I' = -2J`** with the integrability of `g Γ₂(Λ∘g)` and `g Γ(Λ∘g)` (the fourth field of `EntropyInterpolation`). -/
theorem hasDerivAt_entI {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ) (φ : T.A₀) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[T.μ] φ.1) (hφ : ∀ x, φ.1 x ≤ M) (C : BE.Cut ε M)
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun x => T.entG φ ε s x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (T.entG φ ε s y))
      (fun y => C.Λ (T.entG φ ε s y)) x) T.μ ∧
    Integrable (fun x => T.entG φ ε s x * T.toDiffusionTriple.ΓA (fun y => C.Λ (T.entG φ ε s y))
      (fun y => C.Λ (T.entG φ ε s y)) x) T.μ ∧
    HasDerivAt (T.entI φ ε) (-2 * T.entJ C.Λ φ ε s) s := by
  obtain ⟨B, hH⟩ := fisherHyp hCD hρ φ hM h0 hφ s
  obtain ⟨⟨i1, i2⟩, heq⟩ := fisher_alg hCD hH hε C
  refine ⟨i1, i2, ?_⟩
  have hd := hasDerivAt_entI_pair hε hM h0 hφ C hs
  have hQ : T.L (T.Pt s.toNNReal φ) =ᵐ[T.μ] (T.orb (T.Lt φ) s : E → ℝ) := L_Pt_ae φ s
  have hQ2 : T.L (T.L (T.Pt s.toNNReal φ)) =ᵐ[T.μ] (T.orb (T.Lt (T.Lt φ)) s : E → ℝ) := by
    have hQA : T.L (T.Pt s.toNNReal φ) ∈ T.A := L_memA (T.Pt_mem_A _ φ)
    have hQ' : T.Pt s.toNNReal (T.Lt φ) ∈ T.A := T.Pt_mem_A _ _
    exact (L_congr_A T hQA hQ' (hQ.trans (T.orb_ae (T.Lt φ) s))).trans (L_Pt_ae (T.Lt φ) s)
  have e1 : ∫ x, deriv C.Λ (T.gcurve φ ε s x) * (T.orb (T.Lt φ) s : E → ℝ) x *
      (T.orb (T.Lt φ) s : E → ℝ) x ∂T.μ =
      ∫ x, lam1 C (T.Pt s.toNNReal φ x) * T.L (T.Pt s.toNNReal φ) x * T.L (T.Pt s.toNNReal φ) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [T.gcurve_ae φ ε s, hQ] with x h1 h2
    rw [h1, ← h2]; rfl
  have e2 : ∫ x, C.Λ (T.gcurve φ ε s x) * (T.orb (T.Lt (T.Lt φ)) s : E → ℝ) x ∂T.μ =
      ∫ x, lam0 C (T.Pt s.toNNReal φ x) * T.L (T.L (T.Pt s.toNNReal φ)) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [T.gcurve_ae φ ε s, hQ2] with x h1 h2
    rw [h1, ← h2]; rfl
  rw [e1, e2, heq] at hd
  simp only [lam0] at hd
  unfold entJ
  simp only [entG]
  convert hd using 1
  ring

variable (T) in
/-- **`EntropyInterpolation` (G3) for every `FullTriple` of finite measure with `CD(ρ,n)`, `ρ ≥ 0`.** -/
theorem entropyInterpolation {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ) :
    T.EntropyInterpolation where
  continuousOn_E := fun φ _ hε h0 => entE_continuousOn φ hε h0
  continuousOn_I := fun φ _ hε h0 => entI_continuousOn φ hε h0
  hasDerivAt_E := fun φ _ hε h0 _ hs => hasDerivAt_entE φ hε h0 hs
  hasDerivAt_I := fun φ _ _ hε hM h0 hφ C _ hs => hasDerivAt_entI hCD hρ φ hε hM h0 hφ C hs

end FullTriple

end MarkovTriple.BGL
