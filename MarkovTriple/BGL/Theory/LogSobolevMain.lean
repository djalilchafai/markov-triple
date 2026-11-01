import Mathlib
import MarkovTriple.BGL.Theory.Convergence

/-!
# Logarithmic Sobolev inequality from `CD(ρ,∞)`: the main theorems (conditional on
`EntropyInterpolation`, see `LogSobolev.lean`)
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- **Entropy–Fisher inequality**: `Ent(ε + φ) ≤ I(ε+φ)/(2ρ)` (conditional on
`EntropyInterpolation`). -/
theorem ent_le_fisher [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {ρ : ℝ} {n : ℝ≥0∞}
    (hρ : 0 < ρ) (hCD : T.CD ρ n) (φ : T.A₀) (h0 : 0 ≤ᵐ[T.μ] φ.1) {ε : ℝ} (hε : 0 < ε) :
    Ent T.μ (fun x => ε + φ.1 x) ≤
      (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) / (2 * ρ) := by
  obtain ⟨C0, hC0⟩ := T.bounded φ.1 φ.2
  set M : ℝ := max C0 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hφM : ∀ x, φ.1 x ≤ M := fun x => (le_abs_self _).trans ((hC0 x).trans (le_max_left _ _))
  obtain ⟨C⟩ := BE.exists_cut hε hM.le
  set m : ℝ := ε + ∫ x, φ.1 x ∂T.μ with hm
  have key := BE.ent_le_of_decay (e := fun s => T.entE φ ε s - m * Real.log m)
    (q := fun s => -T.entI φ ε s) hρ
    ((hE.continuousOn_E φ ε hε h0).sub continuousOn_const)
    ((hE.continuousOn_I φ ε hε h0).neg)
    (fun s hs => (hE.hasDerivAt_E φ ε hε h0 s hs).sub_const _)
    (fun s hs => by
      obtain ⟨i1, i2, hd⟩ := hE.hasDerivAt_I φ ε M hε hM h0 hφM C s hs
      refine ⟨-(-2 * T.entJ C.Λ φ ε s), hd.neg, ?_⟩
      have hAg := entG_mem_A T φ ε s
      have hΛA := comp_mem_A T C.hΛ hAg
      have hcd := hCD.2 _ hΛA
      have hint : ρ * ∫ x, T.entG φ ε s x * T.toDiffusionTriple.ΓA (fun y => C.Λ (T.entG φ ε s y))
          (fun y => C.Λ (T.entG φ ε s y)) x ∂T.μ ≤ T.entJ C.Λ φ ε s := by
        rw [← integral_const_mul]
        refine integral_mono_ae (i2.const_mul ρ) i1 ?_
        filter_upwards [entG_range T φ hε hM h0 hφM s, hcd] with x hx h2
        have hpos : 0 < T.entG φ ε s x := lt_of_lt_of_le hε hx.1
        have : 0 ≤ (n⁻¹).toReal * (T.L (fun y => C.Λ (T.entG φ ε s y)) x) ^ 2 :=
          mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
        have h3 : ρ * T.toDiffusionTriple.ΓA (fun y => C.Λ (T.entG φ ε s y))
            (fun y => C.Λ (T.entG φ ε s y)) x ≤ T.toDiffusionTriple.Γ₂
            (fun y => C.Λ (T.entG φ ε s y)) (fun y => C.Λ (T.entG φ ε s y)) x := by linarith
        calc ρ * (T.entG φ ε s x * _) = T.entG φ ε s x * (ρ * _) := by ring
          _ ≤ T.entG φ ε s x * _ := mul_le_mul_of_nonneg_left h3 hpos.le
      rw [← entI_eq T φ hε hM h0 hφM C s] at hint
      show -2 * ρ * -T.entI φ ε s ≤ -(-2 * T.entJ C.Λ φ ε s)
      nlinarith [hint])
    (by
      have := (tendsto_entE T hρ hCD φ hε h0).sub_const (m * Real.log m)
      simpa [hm] using this)
  -- identify the end points
  have hφi : Integrable φ.1 T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple φ.2
  have hint : (∫ x, (ε + φ.1 x) ∂T.μ) = m := by
    rw [integral_add (integrable_const ε) hφi]; simp [hm]
  have eE0 : T.entE φ ε 0 = ∫ x, (ε + φ.1 x) * Real.log (ε + φ.1 x) ∂T.μ := by
    unfold entE
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_zero φ] with x hx
    simp only [entG, Real.toNNReal_zero, hx]
  have hEnt : Ent T.μ (fun x => ε + φ.1 x) = T.entE φ ε 0 - m * Real.log m := by
    unfold Ent
    rw [eE0, hint]
  have eI0 : T.entI φ ε 0 = ∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ := by
    unfold entI
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_zero φ, ΓA_shift T ε (T.Pt_mem_A (0 : ℝ).toNNReal φ),
      T.ΓA_congr_A (T.Pt_mem_A (0 : ℝ).toNNReal φ) (T.A₀_le φ.1 φ.2) (by simpa using T.Pt_zero φ)]
      with x hx h1 h2
    have e : T.entG φ ε 0 = fun x => ε + T.Pt 0 φ x := by funext x; simp [entG]
    simp only [Real.toNNReal_zero] at h1 h2
    rw [e, h1, h2]
    show _ / (ε + T.Pt 0 φ x) = _
    rw [hx]
  rw [hEnt]
  have := key
  simp only [neg_neg] at this
  rw [eI0] at this
  exact this

lemma sq_mem_A₀ {f : E → ℝ} (hf : f ∈ T.A₀) : (fun x => f x ^ 2) ∈ T.A₀ := by
  have e : (fun x => f x ^ 2) = f * f := by funext x; simp [sq]
  rw [e]; exact T.A₀.mul_mem hf hf

/-- The bound for `ε + f²`: `Ent(ε + f²) ≤ (2/ρ) ℰ(f)` (conditional on `EntropyInterpolation`). -/
theorem ent_sq_add_le [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {ρ : ℝ} {n : ℝ≥0∞}
    (hρ : 0 < ρ) (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A₀) {ε : ℝ} (hε : 0 < ε) :
    Ent T.μ (fun x => ε + f x ^ 2) ≤ 2 * (1 / ρ) * ∫ x, T.Γ f f x ∂T.μ := by
  set φ : T.A₀ := ⟨fun x => f x ^ 2, sq_mem_A₀ T hf⟩ with hφ
  have h := ent_le_fisher T hE hρ hCD φ (Eventually.of_forall fun x => sq_nonneg (f x)) hε
  have hfA : f ∈ T.A := T.A₀_le f hf
  have hΓi : Integrable (fun x => T.toDiffusionTriple.ΓA f f x) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (ΓA_self_mem_A₀ T hf)
  have hint : (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) ≤
      4 * ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ := by
    rw [← integral_const_mul]
    have hc : (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) =
        ∫ x, 4 * f x ^ 2 * T.toDiffusionTriple.ΓA f f x / (ε + f x ^ 2) ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [ΓA_sq T hfA] with x hx
      simp only [hφ] at hx ⊢
      rw [hx]
    rw [hc]
    refine integral_mono_of_nonneg ?_ (hΓi.const_mul 4) ?_
    · filter_upwards [T.ΓA_nonneg f hfA] with x hx
      simp only [Pi.zero_apply]
      have : 0 ≤ T.toDiffusionTriple.ΓA f f x := hx
      positivity
    · filter_upwards [T.ΓA_nonneg f hfA] with x hx
      have hΓ0 : 0 ≤ T.toDiffusionTriple.ΓA f f x := hx
      have hpos : 0 < ε + f x ^ 2 := by positivity
      rw [div_le_iff₀ hpos]
      nlinarith [sq_nonneg (f x), mul_nonneg hΓ0 hε.le]
  refine h.trans ?_
  have h2ρ : 0 < 2 * ρ := by positivity
  rw [div_le_iff₀ h2ρ]
  have e : ∫ x, T.Γ f f x ∂T.μ = ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ :=
    (integral_congr_ae (DiffusionTriple.ΓA_ae_eq T.toDiffusionTriple hf hf)).symm
  rw [e]
  have : 2 * (1 / ρ) * (∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ) * (2 * ρ) =
      4 * ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ := by
    field_simp; ring
  rw [this]; exact hint

/-- **LSI from `CD(ρ,∞)`** (BGL Prop. 5.7.1), conditional on `EntropyInterpolation`: `ρ > 0`,
probability measure ⇒ `LS(1/ρ, 0)` on `𝒜₀`: `Ent(f²) ≤ (2/ρ) ℰ(f)`. -/
theorem logSobolev_of_CD_infty [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {ρ : ℝ}
    {n : ℝ≥0∞} (hρ : 0 < ρ) (hCD : T.CD ρ n) : T.toDiffusionTriple.LS (1 / ρ) 0 := by
  refine ⟨inferInstance, by positivity, le_refl _, fun f hf => ?_⟩
  have hφ := sq_mem_A₀ T hf
  have h2 : MemLp (fun x => f x ^ 2) 2 T.μ := DiffusionTriple.memLp2 T.toDiffusionTriple hφ
  have hlim := BE.tendsto_Ent_add T.μ h2
  have hle : Ent T.μ (fun x => f x ^ 2) ≤ 2 * (1 / ρ) * ∫ x, T.Γ f f x ∂T.μ := by
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ent_sq_add_le T hE hρ hCD hf hε
  simpa [energy, dirichletForm] using hle

/-- The same on the whole Dirichlet domain. -/
theorem logSobolev_extend_domain [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {ρ : ℝ}
    {n : ℝ≥0∞} (hρ : 0 < ρ) (hCD : T.CD ρ n) (u : T.toDiffusionTriple.formDomain) :
    Integrable (fun x => ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 *
        Real.log (((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2)) T.μ ∧
      Ent T.μ (fun x => ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2) ≤
        2 * (1 / ρ) * T.toDiffusionTriple.closedForm u u +
          0 * ∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ :=
  DiffusionTriple.LS.extend T.toDiffusionTriple (logSobolev_of_CD_infty T hE hρ hCD) u

end FullTriple

end MarkovTriple.BGL
