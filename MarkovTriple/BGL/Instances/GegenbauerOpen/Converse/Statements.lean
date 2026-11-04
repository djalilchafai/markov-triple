import Mathlib
import MarkovTriple.BGL.Theory.Extension.ConverseDirect
import MarkovTriple.BGL.Instances.GegenbauerOpen.Final

/-!
# R24-B: statements (frozen before proofs) -- converse of BGL Prop. 3.3.17 without completeness

Statements only (as `Prop`-valued definitions, no proof); proofs in `Converse/Main.lean`.  See `STATEMENTS_R24_B.md`.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- (S1) `Lf ∈ L²` from `CD(ρ,n)`, `n < ∞`, and `Γ(f), Γ₂(f) ∈ L¹`; no completeness. -/
def R24B_memLp_L (T : FullTriple E) : Prop :=
  ∀ {ρ : ℝ} {n : ℝ≥0∞}, n ≠ ∞ → T.CD ρ n → ∀ {f : E → ℝ}, f ∈ T.A →
    Integrable (FullTriple.G T f f) T.μ → Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ →
    MemLp (T.L f) 2 T.μ

/-- (S2) the converse of Prop. 3.3.17 (same conclusion as `mem_domain_of_Γ₂_direct`), no completeness. -/
def R24B_converse (T : FullTriple E) : Prop :=
  ∀ {ρ : ℝ} {n : ℝ≥0∞}, n ≠ ∞ → T.CD ρ n → ∀ {f : E → ℝ}, f ∈ T.A → ∀ (hf2 : MemLp f 2 T.μ),
    Integrable (FullTriple.G T f f) T.μ → Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ →
    ∃ hF : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain,
      ((T.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] T.L f

end MarkovTriple.BGL

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

/-- (S3) `goFullTriple` (non-complete, `CD(3,4)`): the converse holds, without completeness (no counterexample exists). -/
def R24B_go_statement : Prop :=
  ∀ {f : ℝ → ℝ}, f ∈ goFullTriple.A → ∀ (hf2 : MemLp f 2 goFullTriple.μ),
    Integrable (FullTriple.G goFullTriple f f) goFullTriple.μ →
    Integrable (goFullTriple.toDiffusionTriple.Γ₂ f f) goFullTriple.μ →
    ∃ hF : hf2.toLp f ∈ goFullTriple.toDiffusionTriple.generator.domain,
      ((goFullTriple.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 goFullTriple.μ) : ℝ → ℝ)
        =ᵐ[goFullTriple.μ] goFullTriple.L f

end MarkovTriple.BGL.Instances.GegenbauerOpen
