import Mathlib
import MarkovTriple.BGL.Instances.OUCompact.Triple
import MarkovTriple.BGL.Theory.Compact.Consequences
import MarkovTriple.BGL.Theory.Poincare

/-!
# Unconditional Poincaré and log-Sobolev inequalities on the compact-type OU triple

The first `CompactTriple` with `Γ ≠ 0` and `CD(ρ,·)`, `ρ > 0`: the Ornstein–Uhlenbeck triple
`ouBCompact` (`𝒜 = 𝒜₀ = ℬ`, `CD(1,∞)`).  The theorems of `Theory/Compact/` and `Theory/Poincare.lean`
therefore apply non-vacuously (no hypothesis beyond `CD(1,∞)`, which is proved):

* `ouBCompact_PI`: `Var f ≤ ∫ Γ(f)` for `f ∈ ℬ` (Poincaré with constant `1`, BGL Prop. 4.8.3);
* `ouBCompact_LS`: `LS(1, 0)` (log-Sobolev with constant `1`, `Ent(f²) ≤ 2 ∫ Γ(f)`; Prop. 5.7.1);
* `ouBCompact_gradient_bound`: `Γ(P_t f) ≤ e^{-2t} P_t Γ(f)`;
* `ouBCompact_fisher_decay`: `I(s) ≤ e^{-2s} I(0)` along the heat flow.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL.Instances.OUCompact

instance : IsProbabilityMeasure ouBCompact.toFullTriple.μ :=
  (inferInstance : IsProbabilityMeasure ouB.μ)

/-- **Poincaré inequality** on the compact-type OU triple, from `CD(1,∞)` (unconditional). -/
theorem ouBCompact_PI : ouBCompact.toDiffusionTriple.PI (1 / 1) :=
  FullTriple.poincare_of_CD_infty ouBCompact.toFullTriple one_pos ouBCompact_CD

/-- **Logarithmic Sobolev inequality** `LS(1, 0)` on the compact-type OU triple (unconditional;
`compact_logSobolev` with `ρ = 1`). -/
theorem ouBCompact_LS : ouBCompact.toDiffusionTriple.LS (1 / 1) 0 :=
  compact_logSobolev ouBCompact one_pos ouBCompact_CD

/-- **Gradient bound** `Γ(P_t f) ≤ e^{-2t} P_t Γ(f)` (weak form) on the compact-type OU triple. -/
theorem ouBCompact_gradient_bound (f : ouBCompact.A₀) (t : ℝ≥0) :
    ouBCompact.toDiffusionTriple.ΓA (ouBCompact.Pt t f) (ouBCompact.Pt t f) ≤ᵐ[ouBCompact.μ]
      fun x => Real.exp (-2 * 1 * t) * (ouBCompact.toDiffusionTriple.semigroup t
        (ouBCompact.toDiffusionTriple.cls ⟨ouBCompact.toDiffusionTriple.ΓA f.1 f.1,
          ouBCompact.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 ouBCompact.μ) x :=
  compact_gradient_bound ouBCompact ouBCompact_CD f t

/-- **Decay of the Fisher information** along the heat flow: `I(s) ≤ e^{-2s} I(0)`. -/
theorem ouBCompact_fisher_decay (φ : ouBCompact.A₀) (h0 : 0 ≤ᵐ[ouBCompact.μ] φ.1) {ε : ℝ}
    (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) :
    ouBCompact.toFullTriple.entI φ ε s ≤
      Real.exp (-2 * 1 * s) * ouBCompact.toFullTriple.entI φ ε 0 :=
  ouBCompact.fisher_decay ouBCompact_CD φ h0 hε hs

end MarkovTriple.BGL.Instances.OUCompact

#print axioms MarkovTriple.BGL.Instances.OUCompact.ouBCompact
#print axioms MarkovTriple.BGL.Instances.OUCompact.ouBCompact_CD
#print axioms MarkovTriple.BGL.Instances.OUCompact.ouBCompact_Γ_ne_zero
#print axioms MarkovTriple.BGL.Instances.OUCompact.ouBCompact_PI
#print axioms MarkovTriple.BGL.Instances.OUCompact.ouBCompact_LS
#print axioms MarkovTriple.BGL.Instances.OUCompact.ouBCompact_gradient_bound
#print axioms MarkovTriple.BGL.Instances.OUCompact.ouBCompact_fisher_decay
