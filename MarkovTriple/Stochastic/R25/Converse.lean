import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Main
import MarkovTriple.BGL.Instances.GegenbauerOpen.Converse.Main

/-!
# Round 25 (E), part 5: the finite-`n` converse of BGL Prop. 3.3.17 on `(ℝ^d, Lebesgue)`

An instance of `FullTriple.mem_domain_of_Γ₂_finite` (R24-B) with `ρ = 0`, using `lebesgueRdFull_CD_iff`
(`CD(0, n)` iff `d ≤ n`).  See `STATEMENTS_R25_E.md`.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.Stochastic.R25

open MarkovTriple.BGL MarkovTriple.BGL.LebesgueRd

theorem lebesgueRdFull_mem_domain_of_Γ₂_finite {d : ℕ} (hd : 1 ≤ d) {n : ℝ≥0∞} (hn : n ≠ ∞)
    (hdn : (d : ℝ≥0∞) ≤ n) {f : (Fin d → ℝ) → ℝ} (hf : f ∈ (lebesgueRdFull d hd).A)
    (hf2 : MemLp f 2 (lebesgueRdFull d hd).μ)
    (hG : Integrable (FullTriple.G (lebesgueRdFull d hd) f f) (lebesgueRdFull d hd).μ)
    (hG2 : Integrable ((lebesgueRdFull d hd).toDiffusionTriple.Γ₂ f f) (lebesgueRdFull d hd).μ) :
    ∃ hF : hf2.toLp f ∈ (lebesgueRdFull d hd).toDiffusionTriple.generator.domain,
      (((lebesgueRdFull d hd).toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 (lebesgueRdFull d hd).μ) : (Fin d → ℝ) → ℝ) =ᵐ[(lebesgueRdFull d hd).μ]
        (lebesgueRdFull d hd).L f :=
  FullTriple.mem_domain_of_Γ₂_finite (lebesgueRdFull d hd) hn
    ((lebesgueRdFull_CD_iff hd 0 n).2 ⟨le_rfl, hdn⟩) hf hf2 hG hG2

end MarkovTriple.Stochastic.R25
