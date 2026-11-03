import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Diffusion

/-!
# Gibbs measures: integration by parts against smooth (non compactly supported) functions

BGL Def. 3.3.1 (vii) (F7) for the Gibbs generator `L f = f'' - V' f'`, `𝒜 = C^∞(ℝ)`, `𝒜₀ = C_c^∞(ℝ)`:
for `f, g` smooth with one of them compactly supported, `∫ g L f dμ = -∫ g' f' dμ`.  This is the
ingredient of the book's route to Props. 3.2.1 / 3.3.10 / 3.3.11 (`gibbs_preFull` in `FunctAlgebra`).
-/

open MeasureTheory Filter Topology
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- Integration by parts `∫ g L f dμ = -∫ g' f' dμ` for smooth `f, g`, one of them compactly
supported: F7 (BGL Def. 3.3.1 (vii), `∫ Γ(f,g) = -∫ g L f` for `f ∈ 𝒜`, `g ∈ 𝒜₀`) for the Gibbs
generator on `𝒜 = C^∞`. -/
lemma ibp_sm {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g)
    (hc : HasCompactSupport g ∨ HasCompactSupport f) :
    ∫ x, g x * Lg G.V f x ∂G.μ = -∫ x, deriv g x * deriv f x ∂G.μ := by
  have hgf : HasCompactSupport (fun x => g x * deriv f x) := by
    rcases hc with h | h
    · exact h.mul_right
    · exact h.deriv.mul_left
  have hm := G.ibp_master hf hg hgf
  have c1 : HasCompactSupport (fun x => g x * Lg G.V f x) := by
    rcases hc with h | h
    · exact h.mul_right
    · have : HasCompactSupport (Lg G.V f) := by
        have h2 : HasCompactSupport (fun x => deriv G.V x * deriv f x) := h.deriv.mul_left
        exact h.deriv.deriv.sub h2
      exact this.mul_left
  have c2 : HasCompactSupport (fun x => deriv g x * deriv f x) := by
    rcases hc with h | h
    · exact h.deriv.mul_right
    · exact h.deriv.mul_left
  have i1 : Integrable (fun x => G.w x * (g x * Lg G.V f x)) volume :=
    G.integrable_cs (hg.continuous.mul (sm_Lg G.smooth hf).continuous) c1
  have i2 : Integrable (fun x => G.w x * (deriv g x * deriv f x)) volume :=
    G.integrable_cs (hg.deriv'.continuous.mul hf.deriv'.continuous) c2
  simp only [mul_add] at hm
  rw [integral_add i1 i2] at hm
  rw [G.integral_μ, G.integral_μ]
  linarith

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
