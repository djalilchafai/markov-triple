import Mathlib
import MarkovTriple.FunctionalInequalities.BEFinal
import MarkovTriple.FunctionalInequalities.EntropyIntegrable
import MarkovTriple.Frozen.LSI

/-! # Bakry–Émery (Phase 4b): `CD(ρ,∞) ⟹ LSI(1/ρ)` (modulo `BEStable`) -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E]

/-- `Ent(ε + g) → Ent(g)` as `ε → 0⁺` for `g ∈ L²` (probability measure). -/
theorem tendsto_Ent_add (μ : Measure E) [IsProbabilityMeasure μ] {g : E → ℝ} (hg : MemLp g 2 μ) :
    Tendsto (fun ε : ℝ => MarkovTriple.Ent μ (fun x => ε + g x)) (𝓝[>] 0)
      (𝓝 (MarkovTriple.Ent μ g)) := by
  have hgi : Integrable g μ := hg.integrable one_le_two
  have h1 : Tendsto (fun ε : ℝ => ∫ x, (ε + g x) * Real.log (ε + g x) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, g x * Real.log (g x) ∂μ)) := by
    have hbd : Integrable (fun x => 1 + (1 + |g x|) ^ 2) μ :=
      (integrable_const (1 : ℝ)).add (by
        have := (hg.norm.add (memLp_const (1 : ℝ))).integrable_sq
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp [add_comm])
    refine tendsto_integral_filter_of_dominated_convergence (fun x => 1 + (1 + |g x|) ^ 2)
      ?_ ?_ hbd ?_
    · refine Filter.Eventually.of_forall fun ε => ?_
      exact (Real.continuous_mul_log.comp (continuous_const.add continuous_id)).comp_aestronglyMeasurable
        hg.aestronglyMeasurable
    · have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
      filter_upwards [this] with ε hε
      refine Filter.Eventually.of_forall fun x => ?_
      have h := abs_mul_log_le (ε + g x)
      rw [Real.norm_eq_abs]
      refine h.trans ?_
      have : (ε + g x) ^ 2 ≤ (1 + |g x|) ^ 2 := by
        have h2 : |ε + g x| ≤ 1 + |g x| := by
          calc |ε + g x| ≤ |ε| + |g x| := abs_add_le _ _
            _ ≤ 1 + |g x| := by rw [abs_of_pos hε.1]; linarith [hε.2]
        calc (ε + g x) ^ 2 = |ε + g x| ^ 2 := (sq_abs _).symm
          _ ≤ (1 + |g x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      linarith
    · refine Filter.Eventually.of_forall fun x => ?_
      have : Tendsto (fun ε : ℝ => (ε + g x) * Real.log (ε + g x)) (𝓝 0)
          (𝓝 (g x * Real.log (g x))) := by
        have hc : Continuous (fun ε : ℝ => (ε + g x) * Real.log (ε + g x)) :=
          Real.continuous_mul_log.comp (continuous_id.add continuous_const)
        simpa using hc.tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => (∫ x, (ε + g x) ∂μ) * Real.log (∫ x, (ε + g x) ∂μ)) (𝓝[>] 0)
      (𝓝 ((∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ))) := by
    have e : ∀ ε : ℝ, ∫ x, (ε + g x) ∂μ = ε + ∫ x, g x ∂μ := fun ε => by
      rw [integral_add (integrable_const ε) hgi]; simp
    simp_rw [e]
    have hc : Continuous (fun ε : ℝ => (ε + ∫ x, g x ∂μ) * Real.log (ε + ∫ x, g x ∂μ)) :=
      Real.continuous_mul_log.comp (continuous_id.add continuous_const)
    have := hc.tendsto 0
    simp only [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h1.sub h2

section LSI

variable (F : FullMarkovTriple E)

lemma sq_mem_A₀ {f : E → ℝ} (hf : f ∈ F.A₀) : (fun x => f x ^ 2) ∈ F.A₀ := by
  have e : (fun x => f x ^ 2) = f * f := by funext x; simp [sq]
  rw [e]; exact F.A₀.mul_mem hf hf

lemma Γ_sq {f : E → ℝ} (hf : f ∈ F.A) :
    F.Γ (fun x => f x ^ 2) (fun x => f x ^ 2) = fun x => 4 * f x ^ 2 * F.Γ f f x := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ 2) := contDiff_id.pow 2
  have hg : (fun x => f x ^ 2) ∈ F.A := comp_mem_A F hψ hf
  have h1 := Γ_comp F hψ hf hg
  have h2 := Γ_comp F hψ hf hf
  rw [h1]
  funext x
  have hs := congrFun (F.Γ_symm_A f hf _ hg) x
  have hd : ∀ y : ℝ, deriv (fun y : ℝ => y ^ 2) y = 2 * y := fun y => by simp
  have e2 := congrFun h2 x
  simp only [hd] at e2 ⊢
  rw [hs, e2]; ring

lemma Γ_const_add {φ : E → ℝ} (hφ : φ ∈ F.A) (ε : ℝ) :
    F.Γ (fun x => ε + φ x) (fun x => ε + φ x) = F.Γ φ φ := by
  have hc : (fun _ : E => ε) ∈ F.A := by
    have := F.A.smul_mem F.A.one_mem ε
    have e : (fun _ : E => ε) = ε • (1 : E → ℝ) := by funext x; simp
    rw [e]; exact this
  have hcg : ∀ g ∈ F.A, F.Γ (fun _ : E => ε) g = 0 := by
    intro g hg
    have := F.Γ_smul_A ε 1 F.A.one_mem g hg
    rw [F.Γ_one_left hg] at this
    have e : (fun _ : E => ε) = ε • (1 : E → ℝ) := by funext x; simp
    rw [e, this]; funext x; simp
  have hsum : (fun x => ε + φ x) = (fun _ : E => ε) + φ := rfl
  have hA : (fun x => ε + φ x) ∈ F.A := F.A.add_mem hc hφ
  have e1 : ∀ g ∈ F.A, F.Γ (fun x => ε + φ x) g = F.Γ φ g := by
    intro g hg
    rw [hsum, F.Γ_add_A _ hc φ hφ g hg, hcg g hg]; simp
  rw [e1 _ hA, F.Γ_symm_A φ hφ _ hA, e1 _ hφ]

/-- the entropy bound for `ε + f²`, `f ∈ 𝒜₀`. -/
theorem ent_sq_add_le [IsProbabilityMeasure F.μ] (hB : BEStable F) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : F.CDFull ρ ∞) (herg : F.toMarkovTriple.ErgodicL2) {f : E → ℝ} (hf : f ∈ F.A₀)
    {ε : ℝ} (hε : 0 < ε) :
    MarkovTriple.Ent F.μ (fun x => ε + f x ^ 2) ≤ 2 * (1 / ρ) * F.toMarkovTriple.energy f := by
  have hφ := sq_mem_A₀ F hf
  have hfA : f ∈ F.A := F.A₀_le f hf
  have h := ent_le_fisher F hB hρ hCD herg hφ (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
    hε
  rw [Γ_sq F hfA] at h
  have hΓi : Integrable (fun x => F.Γ f f x) F.μ :=
    integrable_of_mem F.toMarkovTriple (F.Γ_mem f hf f hf)
  have hint : (∫ x, 4 * f x ^ 2 * F.Γ f f x / (ε + f x ^ 2) ∂F.μ) ≤
      4 * F.toMarkovTriple.energy f := by
    have : 4 * F.toMarkovTriple.energy f = ∫ x, 4 * F.Γ f f x ∂F.μ := by
      unfold MarkovTriple.energy
      rw [integral_const_mul]
    rw [this]
    refine integral_mono_of_nonneg ?_ (hΓi.const_mul 4) (Filter.Eventually.of_forall fun x => ?_)
    · refine Filter.Eventually.of_forall fun x => ?_
      have := F.Γ_nonneg_A f hfA x
      simp only [Pi.zero_apply]
      positivity
    · have hΓ0 := F.Γ_nonneg_A f hfA x
      have hpos : 0 < ε + f x ^ 2 := by positivity
      rw [div_le_iff₀ hpos]
      nlinarith [sq_nonneg (f x), mul_nonneg hΓ0 hε.le]
  refine h.trans ?_
  have h2ρ : 0 < 2 * ρ := by positivity
  rw [div_le_iff₀ h2ρ]
  have : 2 * (1 / ρ) * F.toMarkovTriple.energy f * (2 * ρ) = 4 * F.toMarkovTriple.energy f := by
    field_simp; ring
  rw [this]; exact hint

/-- **Bakry–Émery: `CD(ρ,∞) ⟹ LSI(1/ρ)`** for a full Markov triple on a probability space,
under `ρ > 0`, `CDFull ρ ∞`, `ErgodicL2` and the regularity hypothesis `BEStable`. -/
theorem logSobolevIneq_of_CD [IsProbabilityMeasure F.μ] (hB : BEStable F) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : F.CDFull ρ ∞) (herg : F.toMarkovTriple.ErgodicL2) :
    F.toMarkovTriple.LogSobolevIneq (1 / ρ) := by
  refine ⟨inferInstance, fun f hf => ?_⟩
  have hφ := sq_mem_A₀ F hf
  have h2 : MemLp (fun x => f x ^ 2) 2 F.μ := memLp2 F.toMarkovTriple hφ
  have hlim := tendsto_Ent_add F.μ h2
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ent_sq_add_le F hB hρ hCD herg hf hε

/-- **Entropy–Fisher form**: `Ent(ε + φ) ≤ I(ε + φ)/(2ρ)` with the frozen `fisherInfo`. -/
theorem ent_le_fisherInfo [IsProbabilityMeasure F.μ] (hB : BEStable F) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : F.CDFull ρ ∞) (herg : F.toMarkovTriple.ErgodicL2) {φ : E → ℝ} (hφ : φ ∈ F.A₀)
    (h0 : 0 ≤ᵐ[F.μ] φ) {ε : ℝ} (hε : 0 < ε) :
    MarkovTriple.Ent F.μ (fun x => ε + φ x) ≤
      MarkovTriple.fisherInfo F.toMarkovTriple (fun x => ε + φ x) / (2 * ρ) := by
  have := ent_le_fisher F hB hρ hCD herg hφ h0 hε
  have e : MarkovTriple.fisherInfo F.toMarkovTriple (fun x => ε + φ x) =
      ∫ x, F.Γ φ φ x / (ε + φ x) ∂F.μ := by
    unfold MarkovTriple.fisherInfo
    have := Γ_const_add F (F.A₀_le φ hφ) ε
    have e2 : F.toMarkovTriple.Γ (fun x => ε + φ x) (fun x => ε + φ x) = F.Γ φ φ := this
    rw [e2]
  rw [e]; exact this

end LSI

end MarkovTriple.BE
