import Mathlib
import MarkovTriple.Frozen.Ergodic

open MeasureTheory Filter
open scoped Topology ENNReal

namespace MarkovTriple.Audit

variable {E : Type*} [MeasurableSpace E]

private lemma inner_eq_int (μ : Measure E) (a b : Lp ℝ 2 μ) :
    inner ℝ a b = ∫ x, (a : E → ℝ) x * (b : E → ℝ) x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

/-- Any `u` in the kernel of the `L²`-closure of `L|𝒜₀` is orthogonal to `L g`, `g ∈ 𝒜₀`. -/
theorem ker_orth (T : MarkovTriple E) (u : Lp ℝ 2 T.μ) (f : ℕ → E → ℝ) (hf : ∀ n, f n ∈ T.A₀)
    (h1 : Tendsto (fun n => eLpNorm (f n - (u : E → ℝ)) 2 T.μ) atTop (𝓝 0))
    (h2 : Tendsto (fun n => eLpNorm (T.L (f n)) 2 T.μ) atTop (𝓝 0))
    (g : E → ℝ) (hg : g ∈ T.A₀) :
    ∫ x, (u : E → ℝ) x * T.L g x ∂T.μ = 0 := by
  have mf : ∀ n, MemLp (f n) 2 T.μ := fun n => T.memLp _ (hf n) 2 (by norm_num) (by simp)
  have mLf : ∀ n, MemLp (T.L (f n)) 2 T.μ := fun n => T.memLp _ (T.L_mem _ (hf n)) 2 (by norm_num) (by simp)
  have mg : MemLp g 2 T.μ := T.memLp _ hg 2 (by norm_num) (by simp)
  have mLg : MemLp (T.L g) 2 T.μ := T.memLp _ (T.L_mem _ hg) 2 (by norm_num) (by simp)
  set F : ℕ → Lp ℝ 2 T.μ := fun n => (mf n).toLp (f n) with hF
  set G : ℕ → Lp ℝ 2 T.μ := fun n => (mLf n).toLp (T.L (f n)) with hG
  set W : Lp ℝ 2 T.μ := mLg.toLp (T.L g)
  set V : Lp ℝ 2 T.μ := mg.toLp g
  have hFu : Tendsto F atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have : ∀ n, ‖F n - u‖ = (eLpNorm (f n - (u : E → ℝ)) 2 T.μ).toReal := by
      intro n
      rw [Lp.norm_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (F n) u, MemLp.coeFn_toLp (mf n)] with x hx hx2
      rw [hx]; simp only [Pi.sub_apply]; rw [hx2]
    simp_rw [this]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using this
  have hG0 : Tendsto G atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have : ∀ n, ‖G n - 0‖ = (eLpNorm (T.L (f n)) 2 T.μ).toReal := by
      intro n
      rw [sub_zero, Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae (MemLp.coeFn_toLp (mLf n))
    simp_rw [this]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
    simpa [Function.comp_def] using this
  have hsym : ∀ n, inner ℝ (F n) W = inner ℝ (G n) V := by
    intro n
    rw [inner_eq_int, inner_eq_int]
    have e1 : ∫ x, (F n : E → ℝ) x * (W : E → ℝ) x ∂T.μ = ∫ x, f n x * T.L g x ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (mf n), MemLp.coeFn_toLp mLg] with x h h' 
      rw [h, h']
    have e2 : ∫ x, (G n : E → ℝ) x * (V : E → ℝ) x ∂T.μ = ∫ x, g x * T.L (f n) x ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (mLf n), MemLp.coeFn_toLp mg] with x h h'
      rw [h, h', mul_comm]
    rw [e1, e2, T.ibp (f n) (hf n) g hg, T.ibp g hg (f n) (hf n)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [T.Γ_symm _ (hf n) _ hg]
  have lim1 : Tendsto (fun n => inner ℝ (F n) W) atTop (𝓝 (inner ℝ u W)) :=
    (continuous_id.inner continuous_const).tendsto _ |>.comp hFu
  have lim2 : Tendsto (fun n => inner ℝ (G n) V) atTop (𝓝 (inner ℝ (0 : Lp ℝ 2 T.μ) V)) :=
    (continuous_id.inner continuous_const).tendsto _ |>.comp hG0
  simp_rw [hsym] at lim1
  have := tendsto_nhds_unique lim1 lim2
  rw [inner_eq_int] at this
  simp only [inner_zero_left] at this
  rw [← this]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp mLg] with x hx
  rw [hx]

end MarkovTriple.Audit
