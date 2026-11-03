import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.RegBridge

/-!
# Weak hypo-ellipticity of the Gibbs triple (BGL Def. 3.3.8) is a theorem (R15)

`GibbsData.weakHypo : G.WeakHypo` for every `G : GibbsData` (no convexity needed): a `u ∈ L²(μ)` with
`∫ u L a dμ = λ ∫ u a dμ` for all `a ∈ C_c^∞` has a `C^∞` representative.

**Classical theorem formalised**: interior elliptic regularity for `u'' - V' u' = λ u` (BGL Sect. 1.12, p. 157),
proved here in dimension one by du Bois-Reymond + bootstrapping (`RegCore.lean`): `u ∈ C^j ⇒ λ u ∈ C^j ⇒ u ∈ C^{j+2}`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- **`WeakHypo` is a theorem** (BGL Def. 3.3.8 for `e^{-V}dx` on `ℝ`, `𝒜 = C^∞(ℝ)`, all `λ ∈ ℝ`). -/
theorem weakHypo : G.WeakHypo := by
  intro l f hweak
  set u : ℝ → ℝ := (f : ℝ → ℝ) with hu_def
  have hu : Integrable u G.μ := (Lp.memLp f).integrable (by norm_num)
  have hweak' : ∀ a ∈ OA₀, ∫ x, u x * Lg G.V a x ∂G.μ = ∫ x, (fun x => l * u x) x * a x ∂G.μ :=
    fun a ha => hweak ⟨a, ha⟩
  have hh : Integrable (fun x => l * u x) G.μ := hu.const_mul l
  have hQ : ∀ n : ℕ, ∃ U : ℝ → ℝ, ContDiff ℝ (n : WithTop ℕ∞) U ∧ u =ᵐ[volume] U := by
    intro n
    induction n with
    | zero =>
      obtain ⟨U, hU, hae⟩ := G.weak_reg_C1 hu hh hweak'
      exact ⟨U, hU.of_le (by norm_num), hae⟩
    | succ n ih =>
      obtain ⟨U, hU, hae⟩ := ih
      obtain ⟨U', hU', hae'⟩ := G.weak_reg_gain hu hh hweak' n
        ⟨fun x => l * U x, contDiff_const.mul hU, hae.mono fun x hx => by simp [hx]⟩
      refine ⟨U', hU'.of_le ?_, hae'⟩
      push_cast
      have : ((n : WithTop ℕ∞) + 1) ≤ (n : WithTop ℕ∞) + 2 := by
        gcongr; norm_num
      exact this
  obtain ⟨U, hU, hae⟩ := smooth_rep_of_forall hQ
  exact ⟨U, hU, G.ae_mu_of_ae_vol hae⟩

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
