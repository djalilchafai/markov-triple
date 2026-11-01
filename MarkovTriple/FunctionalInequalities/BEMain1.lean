import Mathlib
import MarkovTriple.FunctionalInequalities.BEStable
import MarkovTriple.FunctionalInequalities.BECut
import MarkovTriple.FunctionalInequalities.BENem3

/-! # Bakry–Émery (Phase 4b): the curves `a_r = ε + P_r φ`, `b_r = P_r Lφ` -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

/-- `r ↦ P_r [φ]` (extended by `P_0` for `r < 0`) -/
noncomputable def orb {φ : E → ℝ} (hφ : φ ∈ F.A₀) (r : ℝ) : Lp ℝ 2 F.μ :=
  tripleSemigroup F.toMarkovTriple r.toNNReal (cl F hφ)

/-- `r ↦ ε·1 + P_r [φ]` -/
noncomputable def aflow [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) (ε : ℝ) (r : ℝ) :
    Lp ℝ 2 F.μ := orb F hφ r + ε • oneL2 F.μ

lemma continuous_orb {φ : E → ℝ} (hφ : φ ∈ F.A₀) : Continuous (orb F hφ) :=
  continuous_orbit F _

lemma continuous_aflow [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) (ε : ℝ) :
    Continuous (aflow F hφ ε) :=
  (continuous_orb F hφ).add continuous_const

lemma hasDerivAt_orb {φ : E → ℝ} (hφ : φ ∈ F.A₀) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (orb F hφ) (orb F (F.L_mem φ hφ) s) s :=
  hasDerivAt_orbit F hφ hs

lemma hasDerivAt_aflow [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) (ε : ℝ) {s : ℝ}
    (hs : 0 < s) : HasDerivAt (aflow F hφ ε) (orb F (F.L_mem φ hφ) s) s :=
  (hasDerivAt_orb F hφ hs).add_const _

lemma orb_zero {φ : E → ℝ} (hφ : φ ∈ F.A₀) : orb F hφ 0 = cl F hφ := by
  simp only [orb, Real.toNNReal_zero]
  have := (isSemigroupOf_full F).1
  rw [this]; rfl

section Range

variable {F}

lemma orb_nonneg {φ : E → ℝ} (hφ : φ ∈ F.A₀) (h0 : 0 ≤ᵐ[F.μ] φ) (r : ℝ) :
    0 ≤ᵐ[F.μ] (orb F hφ r : E → ℝ) := by
  have : 0 ≤ᵐ[F.μ] (cl F hφ : E → ℝ) := by
    filter_upwards [coeFn_cl F hφ, h0] with x h1 h2
    rw [h1]; exact h2
  exact ae_nonneg_semigroup this _

lemma orb_abs_le {φ : E → ℝ} (hφ : φ ∈ F.A₀) {M : ℝ} (hM : 0 < M)
    (hb : ∀ᵐ x ∂F.μ, |φ x| ≤ M) (r : ℝ) :
    ∀ᵐ x ∂F.μ, |(orb F hφ r : E → ℝ) x| ≤ M := by
  have : ∀ᵐ x ∂F.μ, |(cl F hφ : E → ℝ) x| ≤ M := by
    filter_upwards [coeFn_cl F hφ, hb] with x h1 h2
    rw [h1]; exact h2
  exact ae_abs_le_semigroup hM this _

lemma aflow_coe [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) (ε r : ℝ) :
    (aflow F hφ ε r : E → ℝ) =ᵐ[F.μ] fun x => (orb F hφ r : E → ℝ) x + ε := by
  have h0 : ((oneL2 F.μ : Lp ℝ 2 F.μ) : E → ℝ) =ᵐ[F.μ] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  filter_upwards [Lp.coeFn_add (orb F hφ r) (ε • oneL2 F.μ),
    Lp.coeFn_smul ε (oneL2 F.μ), h0] with x h1 h2 h3
  rw [aflow, h1]
  simp only [Pi.add_apply]
  rw [h2]; simp [h3]

lemma aflow_range [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) (h0 : 0 ≤ᵐ[F.μ] φ) {M : ℝ}
    (hM : 0 < M) (hb : ∀ᵐ x ∂F.μ, |φ x| ≤ M) (ε r : ℝ) :
    ∀ᵐ x ∂F.μ, (aflow F hφ ε r : E → ℝ) x ∈ Set.Icc ε (ε + M) := by
  filter_upwards [aflow_coe hφ ε r, orb_nonneg hφ h0 r, orb_abs_le hφ hM hb r] with x h1 h2 h3
  rw [h1]
  have := (abs_le.1 h3).2
  exact ⟨by simp only [Pi.zero_apply] at h2; linarith, by linarith⟩

end Range

end MarkovTriple.BE
