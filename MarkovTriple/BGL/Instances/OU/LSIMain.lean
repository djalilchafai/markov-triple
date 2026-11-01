import Mathlib
import MarkovTriple.BGL.Instances.OU.LSIEnt
import MarkovTriple.BGL.Theory.LogSobolevMain

/-!
# OU log-Sobolev / gradient bound (Part 5): `ouFull.EntropyInterpolation` and the unconditional theorems

Bridge from the explicit Mehler-function statements (`LSIEnt`, `LSIGrad`) to the exact statements of
`FullTriple.EntropyInterpolation` (G3) and `FullTriple.GradientInterpolation` (G1), and the resulting
**unconditional** results for the Ornstein–Uhlenbeck triple in the BGL-aligned framework:

* `ouFull_LS : ouFull.toDiffusionTriple.LS 1 0`, i.e. `Ent_γ(f²) ≤ 2 ∫ f'² dγ` for `f ∈ C_c^∞`
  (Gaussian log-Sobolev inequality), and on the whole Dirichlet domain (`ouFull_LS_domain`);
* `ouFull_gradient_bound`: `Γ(P_t f) ≤ e^{-2t} P_t Γ(f)` a.e., for `f ∈ C_c^∞`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

lemma entG_eq (φ : ouFull.A₀) (ε : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ouFull.entG φ ε s = fun x => ε + m0 φ.1 s x := by
  funext x
  show ε + ouFull.Pt s.toNNReal φ x = _
  rw [Pt_eq_m0 φ hs]

lemma entE_eq (φ : ouFull.A₀) (ε : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ouFull.entE φ ε s = eE φ.1 ε s := by
  unfold FullTriple.entE eE
  rw [entG_eq φ ε hs]
  rfl

lemma sm_g (φ : ouFull.A₀) (ε s : ℝ) : Sm (fun x => ε + m0 φ.1 s x) :=
  contDiff_const.add (sm_m0 φ.2 s)

lemma entI_eq (φ : ouFull.A₀) (ε : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ouFull.entI φ ε s = eI φ.1 ε s := by
  unfold FullTriple.entI eI
  rw [entG_eq φ ε hs]
  have hΓ : ouFull.toDiffusionTriple.ΓA (fun x => ε + m0 φ.1 s x) (fun x => ε + m0 φ.1 s x) =
      fun x => m1 φ.1 s x * m1 φ.1 s x :=
    ΓA_eq_of_hasDeriv (sm_g φ ε s) (fun x => (d0x φ.2 s x).const_add ε)
  rw [hΓ]
  rfl

lemma nonneg_φ (φ : ouFull.A₀) (h : 0 ≤ᵐ[ouFull.μ] φ.1) : ∀ x, 0 ≤ φ.1 x :=
  nonneg_of_ae (φ.2.1.continuous) h

lemma bound_φ (φ : ouFull.A₀) : ∃ M, ∀ x, φ.1 x ≤ M := by
  obtain ⟨B, hB⟩ := A₀.bdd φ.2
  exact ⟨B, fun x => (le_abs_self _).trans (hB x)⟩

/-- **G3 for the OU triple**: the entropy interpolation hypothesis is a theorem. -/
theorem ouFull_EntropyInterpolation : ouFull.EntropyInterpolation where
  continuousOn_E := fun φ ε hε h => by
    have h0 := nonneg_φ φ h
    obtain ⟨M, hM⟩ := bound_φ φ
    exact (eE_continuousOn φ.2 h0 hM hε).congr fun s hs => entE_eq φ ε hs
  continuousOn_I := fun φ ε hε h => by
    have h0 := nonneg_φ φ h
    exact (eI_continuousOn φ.2 h0 hε).congr fun s hs => entI_eq φ ε hs
  hasDerivAt_E := fun φ ε hε h s hs => by
    have h0 := nonneg_φ φ h
    obtain ⟨M, hM⟩ := bound_φ φ
    have := eE_hasDerivAt φ.2 h0 hM hε hs
    rw [← entI_eq φ ε hs.le] at this
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with s' hs' using entE_eq φ ε (le_of_lt hs')
  hasDerivAt_I := fun φ ε M hε hM h hφM C s hs => by
    have h0 := nonneg_φ φ h
    have hΛ : (fun y => C.Λ (ouFull.entG φ ε s y)) = fun y => Real.log (ε + m0 φ.1 s y) := by
      funext y
      rw [entG_eq φ ε hs.le]
      exact C.Λ_eq (g_range h0 hφM hε s y)
    have hsmF : Sm (fun y => Real.log (ε + m0 φ.1 s y)) :=
      (sm_g φ ε s).log fun x => (g_pos h0 hε s x).ne'
    have hΓ : ouFull.toDiffusionTriple.ΓA (fun y => Real.log (ε + m0 φ.1 s y))
        (fun y => Real.log (ε + m0 φ.1 s y)) = fun x => F1 φ.1 ε s x * F1 φ.1 ε s x :=
      ΓA_eq_of_hasDeriv hsmF (hasDerivAt_log_g φ.2 h0 hε s)
    have hΓ₂ : ∀ x, ouFull.toDiffusionTriple.Γ₂ (fun y => Real.log (ε + m0 φ.1 s y))
        (fun y => Real.log (ε + m0 φ.1 s y)) x = F2 φ.1 ε s x ^ 2 + F1 φ.1 ε s x ^ 2 := fun x =>
      Γ₂_eq_of_hasDeriv hsmF (hasDerivAt_log_g φ.2 h0 hε s) (hasDerivAt_F1 φ.2 h0 hε s) x
    obtain ⟨hKi, hder⟩ := eI_hasDerivAt φ.2 h0 hε hs
    have hJ : ouFull.entJ C.Λ φ ε s = eJ φ.1 ε s := by
      unfold FullTriple.entJ eJ
      rw [hΛ, entG_eq φ ε hs.le]
      simp only [hΓ₂]
      rfl
    rw [hΛ, entG_eq φ ε hs.le]
    simp only [hΓ, hΓ₂]
    refine ⟨hKi, ?_, ?_⟩
    · have hbd : Bd (Ioi 0) (fun s x => (ε + m0 φ.1 s x) * (F1 φ.1 ε s x * F1 φ.1 ε s x)) :=
        (g_bd φ.2 ε _).mul ((F1_bd φ.2 h0 hε (fun s' hs' => (le_of_lt hs' : (0:ℝ) ≤ s'))).mul
          (F1_bd φ.2 h0 hε (fun s' hs' => (le_of_lt hs' : (0:ℝ) ≤ s'))))
      exact integrable_of_bd ((continuous_const.add (m0_cont φ.2 s)).mul
        ((F1_cont φ.2 h0 hε s).mul (F1_cont φ.2 h0 hε s))) (hbd.at hs)
    · rw [hJ]
      refine hder.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hs] with s' hs' using entI_eq φ ε (le_of_lt hs')

/-- **The Gaussian logarithmic Sobolev inequality, in the BGL-aligned framework, unconditionally**:
`Ent_γ(f²) ≤ 2 ∫ Γ(f) dγ = 2 ∫ f'² dγ` for every `f ∈ C_c^∞(ℝ)` (`LS 1 0` for the OU triple). -/
theorem ouFull_LS : ouFull.toDiffusionTriple.LS 1 0 := by
  haveI : IsProbabilityMeasure ouFull.μ := (inferInstance : IsProbabilityMeasure γ)
  have := FullTriple.logSobolev_of_CD_infty ouFull ouFull_EntropyInterpolation (ρ := 1) one_pos
    ouFull_CD
  simpa using this

/-- The Gaussian LSI on the whole Dirichlet domain. -/
theorem ouFull_LS_domain (u : ouFull.toDiffusionTriple.formDomain) :
    Integrable (fun x => ((u : Lp ℝ 2 ouFull.μ) : ℝ → ℝ) x ^ 2 *
        Real.log (((u : Lp ℝ 2 ouFull.μ) : ℝ → ℝ) x ^ 2)) ouFull.μ ∧
      Ent ouFull.μ (fun x => ((u : Lp ℝ 2 ouFull.μ) : ℝ → ℝ) x ^ 2) ≤
        2 * (1 / 1) * ouFull.toDiffusionTriple.closedForm u u +
          0 * ∫ x, ((u : Lp ℝ 2 ouFull.μ) : ℝ → ℝ) x ^ 2 ∂ouFull.μ := by
  haveI : IsProbabilityMeasure ouFull.μ := (inferInstance : IsProbabilityMeasure γ)
  exact FullTriple.logSobolev_extend_domain ouFull ouFull_EntropyInterpolation (ρ := 1) one_pos
    ouFull_CD u

/-- **Gradient bound for OU, unconditionally**: `Γ(P_t f) ≤ e^{-2t} P_t Γ(f)` a.e. for `f ∈ C_c^∞`. -/
theorem ouFull_gradient_bound (f : ouFull.A₀) (t : ℝ≥0) :
    ouFull.toDiffusionTriple.ΓA (ouFull.Pt t f) (ouFull.Pt t f) ≤ᵐ[ouFull.μ] fun x =>
      Real.exp (-2 * 1 * t) * (ouFull.toDiffusionTriple.semigroup t (ouFull.toDiffusionTriple.cls
        ⟨ouFull.toDiffusionTriple.ΓA f.1 f.1, ouFull.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 ouFull.μ) x :=
  FullTriple.gradient_bound ouFull ouFull_CD ouFull_GradientInterpolation f t

end MarkovTriple.BGL.Instances.OU

#print axioms MarkovTriple.BGL.Instances.OU.ouFull_GradientInterpolation
#print axioms MarkovTriple.BGL.Instances.OU.ouFull_EntropyInterpolation
#print axioms MarkovTriple.BGL.Instances.OU.ouFull_LS
#print axioms MarkovTriple.BGL.Instances.OU.ouFull_LS_domain
#print axioms MarkovTriple.BGL.Instances.OU.ouFull_gradient_bound
