import Mathlib
import MarkovTriple.BGL.Theory.Conservation.Estimate
import MarkovTriple.BGL.Theory.GradientBound

/-!
# Mass conservation under completeness (BGL Thm 3.3.23, first claim; proof of Thm 3.2.6)

**Theorem** (`ExtendedAlgebra.conservative_of_complete`).  Let `D` be a diffusion triple with an extended
algebra `𝒜` (the axioms of `ExtendedAlgebra`), complete (`DiffusionTriple.IsComplete`, Def. 3.3.9), and
assume the weak gradient bound `Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)` (`HasGradientBound`, Cor. 3.3.19).  Then
the semigroup is conservative: for every `t ≥ 0` and every exhaustion sequence `u`, `P_t u_n → 1` a.e.
(S11), *without S11 being assumed*.

Proof (the book's): with `ζ_k` the completeness sequence, `g_k = P_t ζ_k ↑ ℓ ≤ 1`;
`|∫ (g_k − ζ_k) η²| ≤ C(t, η)/(k+1) → 0` (Duhamel + integration by parts + gradient bound, `Estimate.lean`);
dominated convergence gives `∫ (1 − ℓ) η² = 0` for `η = ζ_j`, whence `ℓ = 1`.  The step
`‖√Γ ξ‖₁‖√Γζ_k‖_∞ ≤ ...` of the book is replaced by `2|η|√Γη ≤ η² + Γη`.

The gradient bound itself is the (conditional) content of `Theory/GradientBound.lean`: for full triples it is
available from `GradientInterpolation` (`FullTriple.hasGradientBound`) and unconditionally for compact
triples; the strong form (Thm 3.3.18) is not needed.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace DiffusionTriple

variable (D : DiffusionTriple E)

/-- A complete triple has a nonnegative exhaustion sequence with `Γ(ζ_k) ≤ 1/(k+1)²`. -/
theorem IsComplete.isExhaustion {D : DiffusionTriple E} (hC : D.IsComplete) :
    ∃ ζ : ℕ → E → ℝ, IsExhaustion D.μ D.A₀ ζ ∧ (∀ k, 0 ≤ᵐ[D.μ] ζ k) ∧
      ∀ k, D.Γ (ζ k) (ζ k) ≤ᵐ[D.μ] fun _ => (1 / ((k : ℝ) + 1)) ^ 2 := by
  obtain ⟨ζ, h1, h2, h3, h4, h5⟩ := hC
  exact ⟨ζ, ⟨h1, h3, h4⟩, h2, h5⟩

/-- Sub-Markov bound by a constant: `u ≤ κ ⇒ P_s u ≤ κ` (`κ > 0`). -/
theorem semigroup_le_const (s : ℝ≥0) (u : Lp ℝ 2 D.μ) {κ : ℝ} (hκ : 0 < κ)
    (hu : (u : E → ℝ) ≤ᵐ[D.μ] fun _ => κ) :
    (D.semigroup s u : E → ℝ) ≤ᵐ[D.μ] fun _ => κ := by
  have h1 : ((κ⁻¹ • u : Lp ℝ 2 D.μ) : E → ℝ) ≤ᵐ[D.μ] (1 : E → ℝ) := by
    filter_upwards [hu, Lp.coeFn_smul κ⁻¹ u] with x hx hs
    rw [hs]; simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
    rw [inv_mul_le_iff₀ hκ]; linarith
  have h2 := D.semigroup_le_one s _ h1
  rw [map_smul] at h2
  filter_upwards [h2, Lp.coeFn_smul κ⁻¹ (D.semigroup s u)] with x hx hs
  rw [hs] at hx
  simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hx
  rw [inv_mul_le_iff₀ hκ] at hx; linarith

end DiffusionTriple

namespace ExtendedAlgebra

variable {D : DiffusionTriple E} {A : Subalgebra ℝ (E → ℝ)} (h : ExtendedAlgebra D A)
include h

/-- `|⟪P_t ζ − ζ, η²⟫| ≤ √(e^{2|ρ|t} B) · K(η) · t`. -/
theorem abs_inner_Pt_sub_le {ρ : ℝ} (hGB : HasGradientBound D A ρ) (ζ c : D.A₀)
    (hc : c.1 =ᵐ[D.μ] D.Γ ζ.1 ζ.1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s : ℝ≥0, (D.semigroup s (D.cls c) : E → ℝ) ≤ᵐ[D.μ] fun _ => B)
    (η : D.A₀) (t : ℝ≥0) :
    |inner ℝ (D.semigroup t (D.cls ζ) - D.cls ζ) (D.cls ⟨η.1 * η.1, D.A₀.mul_mem η.2 η.2⟩)| ≤
      Real.sqrt (Real.exp (2 * |ρ| * t) * B) * D.Kconst η * t := by
  rw [D.inner_duhamel]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
    (f := fun s : ℝ => inner ℝ (D.semigroup s.toNNReal (D.Lcls ζ))
      (D.cls ⟨η.1 * η.1, D.A₀.mul_mem η.2 η.2⟩))
    (C := Real.sqrt (Real.exp (2 * |ρ| * t) * B) * D.Kconst η) (fun s hs => by
      rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hs
      obtain ⟨hs0, hst⟩ := hs
      have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0.le
      have hb := h.abs_inner_le hGB ζ c hc hB0 hB η s.toNNReal
      rw [Real.norm_eq_abs]
      refine hb.trans (mul_le_mul_of_nonneg_right ?_ (D.Kconst_nonneg h η))
      refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right ?_ hB0)
      refine Real.exp_le_exp.2 ?_
      rw [hs']
      have : -(ρ) ≤ |ρ| := neg_le_abs ρ
      nlinarith [abs_nonneg ρ])
  simpa [abs_of_nonneg t.2, mul_comm, Real.norm_eq_abs] using this

/-- For the completeness sequence `ζ`, `P_t ζ_k → 1` a.e. -/
theorem tendsto_Pt_complete {ρ : ℝ} (hGB : HasGradientBound D A ρ) (hC : D.IsComplete) (t : ℝ≥0) :
    ∃ (ζ : ℕ → E → ℝ) (hζ : IsExhaustion D.μ D.A₀ ζ), (∀ k, 0 ≤ᵐ[D.μ] ζ k) ∧
      ∀ᵐ x ∂D.μ, Tendsto (fun n => (D.exhP hζ t n : E → ℝ) x) atTop (𝓝 1) := by
  obtain ⟨ζ, hex, hζ0, hζΓ⟩ := hC.isExhaustion
  refine ⟨ζ, hex, hζ0, ?_⟩
  set G : ℕ → E → ℝ := fun k => (D.exhP hex t k : E → ℝ) with hG
  have hGmono : ∀ᵐ x ∂D.μ, Monotone fun k => G k x := D.exhP_monotone_ae hex t
  have hGle : ∀ᵐ x ∂D.μ, ∀ k, G k x ≤ 1 := D.exhP_le_one_ae hex t
  have hG0 : ∀ᵐ x ∂D.μ, ∀ k, 0 ≤ G k x := by
    refine ae_all_iff.2 (fun k => ?_)
    have : 0 ≤ᵐ[D.μ] ((D.cls ⟨ζ k, hex.1 k⟩ : Lp ℝ 2 D.μ) : E → ℝ) := by
      filter_upwards [D.coeFn_cls ⟨ζ k, hex.1 k⟩, hζ0 k] with x h1 h2
      rw [h1]; exact h2
    exact D.semigroup_nonneg t this
  have hζle : ∀ᵐ x ∂D.μ, ∀ k, ζ k x ≤ 1 := hex.le_one_ae
  have hζ0' : ∀ᵐ x ∂D.μ, ∀ k, 0 ≤ ζ k x := ae_all_iff.2 hζ0
  have hζlim := hex.2.2
  set ℓ : E → ℝ := fun x => ⨆ k, G k x with hℓ
  have hGℓ : ∀ᵐ x ∂D.μ, Tendsto (fun k => G k x) atTop (𝓝 (ℓ x)) := by
    filter_upwards [hGmono, hGle] with x h1 h2
    exact tendsto_atTop_ciSup h1 ⟨1, by rintro _ ⟨k, rfl⟩; exact h2 k⟩
  have hGm : ∀ k, AEStronglyMeasurable (G k) D.μ := fun k => Lp.aestronglyMeasurable _
  have hζm : ∀ k, AEStronglyMeasurable (ζ k) D.μ := fun k =>
    (D.measurable _ (hex.1 k)).aestronglyMeasurable
  have hj : ∀ j, ∀ᵐ x ∂D.μ, (1 - ℓ x) * (ζ j x * ζ j x) = 0 := by
    intro j
    set η : D.A₀ := ⟨ζ j, hex.1 j⟩ with hη
    set ξ : D.A₀ := ⟨η.1 * η.1, D.A₀.mul_mem η.2 η.2⟩ with hξ
    have hξx : ∀ x, ξ.1 x = ζ j x * ζ j x := fun x => rfl
    have hξint : Integrable ξ.1 D.μ := D.integrable_of_mem ξ.2
    have hξm : AEStronglyMeasurable ξ.1 D.μ := (D.measurable _ ξ.2).aestronglyMeasurable
    have hξ0 : ∀ x, 0 ≤ ξ.1 x := fun x => by rw [hξx]; exact mul_self_nonneg _
    -- integrability of bounded multiples of ξ
    have hint : ∀ f : E → ℝ, AEStronglyMeasurable f D.μ → (∀ᵐ x ∂D.μ, |f x| ≤ 1) →
        Integrable (fun x => f x * ξ.1 x) D.μ := by
      intro f hf hb
      refine hξint.mono' (hf.mul hξm) ?_
      filter_upwards [hb] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hξ0 x)]
      exact mul_le_of_le_one_left (hξ0 x) hx
    have hb1 : ∀ᵐ x ∂D.μ, ∀ k, |1 - ζ k x| ≤ 1 := by
      filter_upwards [hζle, hζ0'] with x h1 h2 k
      rw [abs_le]; constructor <;> linarith [h1 k, h2 k]
    have hb2 : ∀ᵐ x ∂D.μ, ∀ k, |G k x - ζ k x| ≤ 1 := by
      filter_upwards [hζle, hζ0', hGle, hG0] with x h1 h2 h3 h4 k
      rw [abs_le]; constructor <;> linarith [h1 k, h2 k, h3 k, h4 k]
    have hb3 : ∀ᵐ x ∂D.μ, ∀ k, |1 - G k x| ≤ 1 := by
      filter_upwards [hGle, hG0] with x h3 h4 k
      rw [abs_le]; constructor <;> linarith [h3 k, h4 k]
    -- (T1)
    have hT1 : Tendsto (fun k => ∫ x, (1 - ζ k x) * ξ.1 x ∂D.μ) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := D.μ) ξ.1
        (F := fun k x => (1 - ζ k x) * ξ.1 x) (f := fun _ => (0 : ℝ))
        (fun k => (aestronglyMeasurable_const.sub (hζm k)).mul hξm)
        hξint
        (fun k => by
          filter_upwards [hb1] with x hx
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hξ0 x)]
          exact mul_le_of_le_one_left (hξ0 x) (hx k))
        (by
          filter_upwards [hζlim] with x hx
          have h1 : Tendsto (fun k => 1 - ζ k x) atTop (𝓝 (1 - 1)) := tendsto_const_nhds.sub hx
          simpa using h1.mul_const (ξ.1 x))
      simpa using this
    -- (T2)
    set K := D.Kconst η with hK
    have hT2 : Tendsto (fun k => ∫ x, (G k x - ζ k x) * ξ.1 x ∂D.μ) atTop (𝓝 0) := by
      have hk : ∀ k, |∫ x, (G k x - ζ k x) * ξ.1 x ∂D.μ| ≤
          Real.sqrt (Real.exp (2 * |ρ| * t)) * (1 / ((k : ℝ) + 1)) * K * t := by
        intro k
        set c : D.A₀ := ⟨D.Γ (ζ k) (ζ k), D.Γ_mem _ (hex.1 k) _ (hex.1 k)⟩ with hc
        have hBk : ∀ s : ℝ≥0, (D.semigroup s (D.cls c) : E → ℝ) ≤ᵐ[D.μ]
            fun _ => (1 / ((k : ℝ) + 1)) ^ 2 := by
          intro s
          refine D.semigroup_le_const s _ (by positivity) ?_
          filter_upwards [D.coeFn_cls c, hζΓ k] with x h1 h2
          rw [h1]; exact h2
        have hb := h.abs_inner_Pt_sub_le hGB ⟨ζ k, hex.1 k⟩ c (Filter.EventuallyEq.refl _ _)
          (by positivity) hBk η t
        have e : inner ℝ (D.semigroup t (D.cls ⟨ζ k, hex.1 k⟩) - D.cls ⟨ζ k, hex.1 k⟩)
            (D.cls ξ) = ∫ x, (G k x - ζ k x) * ξ.1 x ∂D.μ := by
          rw [L2_inner_eq]
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_sub (D.semigroup t (D.cls ⟨ζ k, hex.1 k⟩))
            (D.cls ⟨ζ k, hex.1 k⟩), D.coeFn_cls ⟨ζ k, hex.1 k⟩, D.coeFn_cls ξ] with x h1 h2 h3
          rw [h1, Pi.sub_apply, h2, h3]
          rfl
        rw [← e]
        refine hb.trans ?_
        rw [Real.sqrt_mul (Real.exp_pos _).le, Real.sqrt_sq (by positivity)]
      refine squeeze_zero_norm (fun k => ?_) (a := fun k : ℕ =>
        Real.sqrt (Real.exp (2 * |ρ| * t)) * (1 / ((k : ℝ) + 1)) * K * t) ?_
      · rw [Real.norm_eq_abs]; exact hk k
      · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
          (Real.sqrt (Real.exp (2 * |ρ| * t)))
        have := (this.mul_const K).mul_const (t : ℝ)
        simpa using this
    -- ∫ F_k → 0
    have hF : Tendsto (fun k => ∫ x, (1 - G k x) * ξ.1 x ∂D.μ) atTop (𝓝 0) := by
      have e : ∀ k, ∫ x, (1 - G k x) * ξ.1 x ∂D.μ =
          ∫ x, (1 - ζ k x) * ξ.1 x ∂D.μ - ∫ x, (G k x - ζ k x) * ξ.1 x ∂D.μ := by
        intro k
        rw [← integral_sub]
        · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only; ring
        · exact hint _ (aestronglyMeasurable_const.sub (hζm k)) (by
            filter_upwards [hb1] with x hx using hx k)
        · exact hint _ ((hGm k).sub (hζm k)) (by filter_upwards [hb2] with x hx using hx k)
      simp_rw [e]
      simpa using hT1.sub hT2
    -- dominated convergence for F_k → F_∞
    have hlim := tendsto_integral_of_dominated_convergence (μ := D.μ) ξ.1
      (F := fun k x => (1 - G k x) * ξ.1 x) (f := fun x => (1 - ℓ x) * ξ.1 x)
      (fun k => (aestronglyMeasurable_const.sub (hGm k)).mul hξm) hξint
      (fun k => by
        filter_upwards [hb3] with x hx
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hξ0 x)]
        exact mul_le_of_le_one_left (hξ0 x) (hx k))
      (by
        filter_upwards [hGℓ] with x hx
        exact (tendsto_const_nhds.sub hx).mul_const (ξ.1 x))
    have h0 : ∫ x, (1 - ℓ x) * ξ.1 x ∂D.μ = 0 := tendsto_nhds_unique hlim hF
    -- nonnegativity and integrability of F_∞
    have hℓle : ∀ᵐ x ∂D.μ, ℓ x ≤ 1 := by
      filter_upwards [hGℓ, hGle] with x h1 h2
      exact le_of_tendsto' h1 h2
    have hℓ0 : ∀ᵐ x ∂D.μ, 0 ≤ ℓ x := by
      filter_upwards [hGℓ, hG0] with x h1 h2
      exact ge_of_tendsto' h1 h2
    have hFm : AEStronglyMeasurable (fun x => (1 - ℓ x) * ξ.1 x) D.μ := by
      have : AEStronglyMeasurable (fun x => 1 - ℓ x) D.μ := by
        refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun k x => 1 - G k x)
          (fun k => aestronglyMeasurable_const.sub (hGm k)) ?_
        filter_upwards [hGℓ] with x hx
        exact tendsto_const_nhds.sub hx
      exact this.mul hξm
    have hFint : Integrable (fun x => (1 - ℓ x) * ξ.1 x) D.μ := by
      refine hξint.mono' hFm ?_
      filter_upwards [hℓle, hℓ0] with x h1 h2
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hξ0 x),
        abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_left (hξ0 x) (by linarith)
    have hnn : 0 ≤ᵐ[D.μ] fun x => (1 - ℓ x) * ξ.1 x := by
      filter_upwards [hℓle] with x h1
      exact mul_nonneg (by linarith) (hξ0 x)
    have := (integral_eq_zero_iff_of_nonneg_ae hnn hFint).1 h0
    filter_upwards [this] with x hx
    simpa [hξx] using hx
  filter_upwards [ae_all_iff.2 hj, hGℓ, hζlim] with x hx hl hz
  obtain ⟨j, hj0⟩ : ∃ j, 0 < ζ j x := (hz.eventually (lt_mem_nhds one_pos)).exists
  have h1 := hx j
  have hpos : 0 < ζ j x * ζ j x := mul_pos hj0 hj0
  have h2 : 1 - ℓ x = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h hpos.ne'
  have hℓ1 : ℓ x = 1 := by linarith
  rw [hℓ1] at hl
  exact hl

/-- **Mass conservation under completeness (BGL Thm 3.3.23, first claim).**  Complete + weak gradient
bound `⇒` for every exhaustion sequence `u` and `t ≥ 0`, `P_t u_n → 1` a.e. (S11). -/
theorem conservative_of_complete {ρ : ℝ} (hGB : HasGradientBound D A ρ) (hC : D.IsComplete)
    {u : ℕ → E → ℝ} (hu : IsExhaustion D.μ D.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂D.μ, Tendsto (fun n => (D.exhP hu t n : E → ℝ) x) atTop (𝓝 1) := by
  obtain ⟨ζ, hζ, _, hlim⟩ := h.tendsto_Pt_complete hGB hC t
  exact D.conservative_transfer hu hζ t hlim

end ExtendedAlgebra

/-- The gradient bound for full triples, from the interpolation hypothesis (`GradientBound.lean`). -/
theorem FullTriple.hasGradientBound {ρ : ℝ} {n : ℝ≥0∞} (T : FullTriple E) (hCD : T.CD ρ n)
    (hG : T.GradientInterpolation) : HasGradientBound T.toDiffusionTriple T.A ρ := by
  intro f c hc t g hg hPg
  have h1 := T.gradient_bound hCD hG f t
  have e1 : T.toDiffusionTriple.ΓA g g =ᵐ[T.μ] T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) :=
    T.ΓA_congr_A hg (T.Pt_mem_A t f) (hPg.symm.trans (T.Pt_ae t f))
  have e2 : T.toDiffusionTriple.cls c = T.toDiffusionTriple.cls
      ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩ := by
    refine Lp.ext ?_
    filter_upwards [T.toDiffusionTriple.coeFn_cls c, hc,
      T.toDiffusionTriple.ΓA_ae_eq f.2 f.2, T.toDiffusionTriple.coeFn_cls
        ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩] with x a b d e
    rw [a, e]; exact b.trans d.symm
  rw [e2]
  filter_upwards [e1, h1] with x a b
  exact a.le.trans b

/-- `Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)` for full triples satisfying the interpolation hypothesis, so that
completeness gives conservativeness *without S11* (`conservative_of_complete`). -/
theorem FullTriple.conservative_of_complete {ρ : ℝ} {n : ℝ≥0∞} (T : FullTriple E)
    (hCD : T.CD ρ n) (hG : T.GradientInterpolation) (hC : T.toDiffusionTriple.IsComplete)
    {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, Tendsto (fun m => (T.toDiffusionTriple.exhP hu t m : E → ℝ) x) atTop (𝓝 1) :=
  T.extendedAlgebra.conservative_of_complete (T.hasGradientBound hCD hG) hC hu t

end MarkovTriple.BGL
