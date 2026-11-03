import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.RegCore

/-!
# From `L²(μ)` weak solutions to the Lebesgue-level regularity theorem (R15)

Translates the weak equation `∫ u L a dμ = ∫ h a dμ` (`a ∈ 𝒜₀ = C_c^∞`, `μ = w dx`) into the `dx`-form used in
`RegCore.lean` and derives, for `u, h ∈ L¹(μ)`:

* `weak_reg_C1`: `u` has a `C¹` representative;
* `weak_reg_gain`: if `h` has a `C^j` representative, `u` has a `C^{j+2}` representative.

All representatives are with respect to Lebesgue measure (equivalent to `μ` since `w > 0`), see `ae_mu_of_ae_vol`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- `u ∈ L¹(μ)` ⇒ `w u ∈ L¹(dx)`. -/
lemma integrable_w_mul {u : ℝ → ℝ} (hu : Integrable u G.μ) :
    Integrable (fun x => G.w x * u x) volume := by
  have h := (integrable_withDensity_iff_integrable_smul'
    (f := fun x => ENNReal.ofReal (G.w x)) (μ := volume)
    (ENNReal.measurable_ofReal.comp G.w_smooth.continuous.measurable)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hu
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (G.w_pos x).le]

/-- Lebesgue-a.e. equalities are `μ`-a.e. equalities. -/
lemma ae_mu_of_ae_vol {P : ℝ → Prop} (h : ∀ᵐ x ∂volume, P x) : ∀ᵐ x ∂G.μ, P x :=
  (withDensity_absolutelyContinuous volume _).ae_le h

/-- The weak equation in `μ`-form gives the `dx`-form of `RegCore`. -/
lemma weak_vol {u h : ℝ → ℝ}
    (hweak : ∀ a ∈ OA₀, ∫ x, u x * Lg G.V a x ∂G.μ = ∫ x, h x * a x ∂G.μ) :
    ∀ a : ℝ → ℝ, Sm a → HasCompactSupport a →
      ∫ x, G.w x * (u x * Lg G.V a x) = ∫ x, G.w x * (h x * a x) := by
  intro a ha hc
  have := hweak a ⟨ha, hc⟩
  rwa [integral_μ, integral_μ] at this

/-- **Weak solutions in `L¹(μ)` of `L u = h` have a `C¹` representative.** -/
theorem weak_reg_C1 {u h : ℝ → ℝ} (hu : Integrable u G.μ) (hh : Integrable h G.μ)
    (hweak : ∀ a ∈ OA₀, ∫ x, u x * Lg G.V a x ∂G.μ = ∫ x, h x * a x ∂G.μ) :
    ∃ U : ℝ → ℝ, ContDiff ℝ 1 U ∧ u =ᵐ[volume] U := by
  obtain ⟨U, c, hU, hae, -⟩ :=
    G.reg_core (G.integrable_w_mul hu) (G.integrable_w_mul hh) (G.weak_vol hweak)
  exact ⟨U, hU, hae⟩

/-- **Regularity gain**: if moreover `h` has a `C^j` representative then `u` has a `C^{j+2}` one. -/
theorem weak_reg_gain {u h : ℝ → ℝ} (hu : Integrable u G.μ) (hh : Integrable h G.μ)
    (hweak : ∀ a ∈ OA₀, ∫ x, u x * Lg G.V a x ∂G.μ = ∫ x, h x * a x ∂G.μ) (j : ℕ)
    (hj : ∃ ht : ℝ → ℝ, ContDiff ℝ (j : WithTop ℕ∞) ht ∧ h =ᵐ[volume] ht) :
    ∃ U : ℝ → ℝ, ContDiff ℝ ((j : WithTop ℕ∞) + 2) U ∧ u =ᵐ[volume] U := by
  obtain ⟨ht, hht, hae⟩ := hj
  exact G.reg_core_smooth j (G.integrable_w_mul hu) (G.integrable_w_mul hh) (G.weak_vol hweak) hht hae

/-- Two continuous functions that agree Lebesgue-a.e. agree everywhere. -/
lemma eq_of_ae_vol {U V : ℝ → ℝ} (hU : Continuous U) (hV : Continuous V)
    (h : U =ᵐ[volume] V) : U = V :=
  (Continuous.ae_eq_iff_eq volume hU hV).1 h

/-- A function that has, for every `n`, a `C^n` representative (Lebesgue-a.e.) has a `C^∞` representative. -/
lemma smooth_rep_of_forall {u : ℝ → ℝ}
    (h : ∀ n : ℕ, ∃ U : ℝ → ℝ, ContDiff ℝ (n : WithTop ℕ∞) U ∧ u =ᵐ[volume] U) :
    ∃ U : ℝ → ℝ, Sm U ∧ u =ᵐ[volume] U := by
  obtain ⟨U0, hU0, hu0⟩ := h 0
  refine ⟨U0, ?_, hu0⟩
  refine contDiff_infty.2 (fun n => ?_)
  obtain ⟨Un, hUn, hun⟩ := h n
  have : U0 = Un := eq_of_ae_vol hU0.continuous hUn.continuous (hu0.symm.trans hun)
  rw [this]; exact hUn

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
