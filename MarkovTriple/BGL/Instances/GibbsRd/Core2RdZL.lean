import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Calculus

/-!
# `Core2` on `ℝ^d`: sequences tending to `0` in `L²(μ)` (R18, Stream A3; bookkeeping)

`ZL μ D`: `D n ∈ L²(μ)` and `[D n] → 0`.  `Good c`: continuous, uniformly bounded families vanishing eventually at every
point; `Good c × fixed L² function` is `ZL` (dominated convergence).  Generic in the measure `μ` on `ℝ^d`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ} {μ : Measure (Rd d)}

/-- `‖[g]‖² = ∫ g²`. -/
lemma norm_toLp_sq_rd {g : Rd d → ℝ} (hg : MemLp g 2 μ) : ‖hg.toLp g‖ ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]
  simp [sq]

lemma tendsto_toLp_zero_rd {G : ℕ → Rd d → ℝ} (hG : ∀ n, MemLp (G n) 2 μ)
    (h : Tendsto (fun n => ∫ x, (G n x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ n, ‖(hG n).toLp (G n) - 0‖ = Real.sqrt (∫ x, (G n x) ^ 2 ∂μ) := by
    intro n
    rw [sub_zero, ← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq_rd (hG n)]
  simp only [e]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  exact this

/-- `D n → 0` in `L²(μ)` (with the `L²` memberships). -/
def ZL (μ : Measure (Rd d)) (D : ℕ → Rd d → ℝ) : Prop :=
  ∃ h : ∀ n, MemLp (D n) 2 μ, Tendsto (fun n => (h n).toLp (D n)) atTop (𝓝 0)

lemma ZL.zero : ZL μ (fun _ _ => (0 : ℝ)) := by
  refine ⟨fun n => MemLp.zero, ?_⟩
  have : ∀ n : ℕ, (MemLp.zero : MemLp (fun _ : Rd d => (0 : ℝ)) 2 μ).toLp (fun _ => 0) = 0 := fun n =>
    Lp.ext (by
      filter_upwards [(MemLp.zero : MemLp (fun _ : Rd d => (0 : ℝ)) 2 μ).coeFn_toLp, Lp.coeFn_zero ℝ 2 μ]
        with x h1 h2
      exact h1.trans h2.symm)
  exact tendsto_const_nhds.congr (fun n => (this n).symm)

lemma ZL.add {D₁ D₂ : ℕ → Rd d → ℝ} (h₁ : ZL μ D₁) (h₂ : ZL μ D₂) :
    ZL μ (fun n x => D₁ n x + D₂ n x) := by
  obtain ⟨m₁, t₁⟩ := h₁; obtain ⟨m₂, t₂⟩ := h₂
  refine ⟨fun n => (m₁ n).add (m₂ n), ?_⟩
  have := t₁.add t₂
  rw [add_zero] at this
  refine this.congr (fun n => ?_)
  rw [← MemLp.toLp_add]; rfl

lemma ZL.sub {D₁ D₂ : ℕ → Rd d → ℝ} (h₁ : ZL μ D₁) (h₂ : ZL μ D₂) :
    ZL μ (fun n x => D₁ n x - D₂ n x) := by
  obtain ⟨m₁, t₁⟩ := h₁; obtain ⟨m₂, t₂⟩ := h₂
  refine ⟨fun n => (m₁ n).sub (m₂ n), ?_⟩
  have := t₁.sub t₂
  rw [sub_zero] at this
  refine this.congr (fun n => ?_)
  rw [← MemLp.toLp_sub]; rfl

lemma ZL.congr {D D' : ℕ → Rd d → ℝ} (h : ZL μ D) (e : ∀ n x, D n x = D' n x) : ZL μ D' := by
  have : D = D' := funext fun n => funext fun x => e n x
  rwa [← this]

lemma ZL.const_mul {D : ℕ → Rd d → ℝ} (h : ZL μ D) (c : ℝ) : ZL μ (fun n x => c * D n x) := by
  obtain ⟨m, t⟩ := h
  refine ⟨fun n => (m n).const_mul c, ?_⟩
  have := t.const_smul c
  rw [smul_zero] at this
  refine this.congr (fun n => ?_)
  rw [← MemLp.toLp_const_smul]; rfl

lemma ZL.finset_sum {ι : Type*} (s : Finset ι) {D : ι → ℕ → Rd d → ℝ} (h : ∀ i ∈ s, ZL μ (D i)) :
    ZL μ (fun n x => ∑ i ∈ s, D i n x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ZL.zero
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact (h1.add h2).congr (fun n x => by rw [Finset.sum_insert ha])

/-- uniformly bounded families -/
def UB (f : ℕ → Rd d → ℝ) : Prop := ∃ C : ℝ, ∀ n x, |f n x| ≤ C

/-- `Good` coefficient families: continuous, uniformly bounded, eventually `0` at every point. -/
def Good (c : ℕ → Rd d → ℝ) : Prop :=
  (∀ n, Continuous (c n)) ∧ UB c ∧ ∀ x, ∀ᶠ n in atTop, c n x = 0

/-- bounded continuous coefficients, vanishing eventually at every point, times a fixed `L²` function. -/
lemma ZL.of_good {c : ℕ → Rd d → ℝ} (hc : Good c) {g : Rd d → ℝ} (hg : MemLp g 2 μ) :
    ZL μ (fun n x => c n x * g x) := by
  obtain ⟨hcont, ⟨K, hK⟩, hz⟩ := hc
  have hm : ∀ n, MemLp (fun x => c n x * g x) 2 μ := fun n =>
    hg.of_le_mul (c := K) ((hcont n).aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hK n x) (abs_nonneg _))
  refine ⟨hm, tendsto_toLp_zero_rd hm ?_⟩
  have hg2 : Integrable (fun x => (g x) ^ 2) μ := hg.integrable_sq
  have := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun (n : ℕ) x => (c n x * g x) ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => K ^ 2 * (g x) ^ 2)
    (fun n => (((hcont n).aestronglyMeasurable.mul hg.aestronglyMeasurable).pow 2))
    (hg2.const_mul _)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_mul_of_nonneg_right (by nlinarith [hK n x, abs_nonneg (c n x), sq_abs (c n x)])
        (sq_nonneg _))
    (Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hz x] with n hn
      rw [hn]; simp)
  simpa using this

lemma UB.add {f g : ℕ → Rd d → ℝ} (hf : UB f) (hg : UB g) : UB (fun n x => f n x + g n x) := by
  obtain ⟨C, hC⟩ := hf; obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun n x => (abs_add_le _ _).trans (add_le_add (hC n x) (hD n x))⟩

lemma UB.mul {f g : ℕ → Rd d → ℝ} (hf : UB f) (hg : UB g) : UB (fun n x => f n x * g n x) := by
  obtain ⟨C, hC⟩ := hf; obtain ⟨D, hD⟩ := hg
  refine ⟨C * D, fun n x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC n x) (hD n x) (abs_nonneg _) ((abs_nonneg _).trans (hC n x))

end MarkovTriple.BGL.Instances.GibbsRd
