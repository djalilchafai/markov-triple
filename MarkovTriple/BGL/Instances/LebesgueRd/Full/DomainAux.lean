import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Gamma2

/-!
# Cut-off approximation in `L²(ℝ^d)` (Round 24, stream A, part B-a, helper file)

Port of `Instances/Lebesgue/Cutoff.lean` to `ℝ^d`, with the scaled cut-offs `cut n x = ζ₀ (x/(n+1))`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

lemma norm_toLp_sq' {g : (Fin d → ℝ) → ℝ} (hg : MemLp g 2 volume) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, (g x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]
  simp

/-- bounded continuous multipliers tending to `0` pointwise send `w ∈ L²` to `0` in `L²`. -/
lemma tendsto_toLp_mul_zero {m : ℕ → (Fin d → ℝ) → ℝ} (hm : ∀ n, Continuous (m n)) {c : ℝ}
    (hc : ∀ n x, |m n x| ≤ c) (hlim : ∀ x, Tendsto (fun n => m n x) atTop (𝓝 0))
    {w : (Fin d → ℝ) → ℝ} (hw : MemLp w 2 volume)
    (hmw : ∀ n, MemLp (fun x => m n x * w x) 2 volume) :
    Tendsto (fun n => (hmw n).toLp (fun x => m n x * w x)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have e : ∀ n, ‖(hmw n).toLp (fun x => m n x * w x)‖ =
      Real.sqrt (∫ x, (m n x * w x) ^ 2) := fun n => by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq']
  simp only [e]
  have hw2 : Integrable (fun x => (w x) ^ 2) := hw.integrable_sq
  have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Fin d → ℝ)))
    (F := fun (n : ℕ) x => (m n x * w x) ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => c ^ 2 * (w x) ^ 2)
    (fun n => (((hm n).aestronglyMeasurable).mul hw.aestronglyMeasurable).pow 2)
    (hw2.const_mul _)
    (fun n => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_mul_of_nonneg_right (by nlinarith [hc n x, abs_nonneg (m n x), sq_abs (m n x)])
        (sq_nonneg _))
    (Filter.Eventually.of_forall fun x => by
      have := ((hlim x).mul_const (w x)).pow 2
      simpa using this)
  rw [integral_zero] at this
  have h2 := (Real.continuous_sqrt.tendsto 0).comp this
  rw [Real.sqrt_zero] at h2
  exact h2

lemma coeFn_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℝ 2 (volume : Measure (Fin d → ℝ))) :
    ((∑ i ∈ s, f i : Lp ℝ 2 (volume : Measure (Fin d → ℝ))) : (Fin d → ℝ) → ℝ) =ᵐ[volume]
      fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure (Fin d → ℝ))] with x _
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

/-! ### Scaling -/

lemma sq_smul (c : ℝ) (x : Fin d → ℝ) : sq (c • x) = c ^ 2 * sq x := by
  unfold sq
  simp [mul_pow, Finset.mul_sum]

lemma dd_scale {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (c : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    dd i (fun y => f (c • y)) x = c * dd i f (c • x) := by
  have h1 : HasFDerivAt (fun y : Fin d → ℝ => c • y) (c • ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
    (hasFDerivAt_id x).const_smul c
  have h2 := (hasFDerivAt_of hf (c • x)).comp x h1
  unfold dd
  have h3 : fderiv ℝ (fun y => f (c • y)) x = _ := h2.fderiv
  rw [h3]
  simp

lemma sm_scale {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (c : ℝ) : Sm (fun y => f (c • y)) :=
  hf.comp (contDiff_id.const_smul c : ContDiff ℝ (⊤ : ℕ∞) fun y : Fin d → ℝ => c • y)

lemma dd_dd_scale {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (c : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    dd i (dd i fun y => f (c • y)) x = c ^ 2 * dd i (dd i f) (c • x) := by
  have e : dd i (fun y => f (c • y)) = fun y => c * dd i f (c • y) := funext (dd_scale hf c i)
  rw [e]
  have h := (hf.dd i)
  have e2 : (fun y => c * dd i f (c • y)) = c • (fun y => dd i f (c • y)) := rfl
  rw [e2, dd_smul c (sm_scale h c) i]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [dd_scale h c i x]
  ring

/-! ### Bounds for the cut-offs -/

lemma cut_eq_scale (n : ℕ) (x : Fin d → ℝ) :
    (cut n : (Fin d → ℝ) → ℝ) x = (cut 0 : (Fin d → ℝ) → ℝ) (((n : ℝ) + 1)⁻¹ • x) := by
  unfold cut
  rw [sq_smul]
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  congr 2
  push_cast
  field_simp
  simp

lemma cut_eq_scale' (n : ℕ) :
    (cut n : (Fin d → ℝ) → ℝ) = fun x => (cut 0 : (Fin d → ℝ) → ℝ) (((n : ℝ) + 1)⁻¹ • x) :=
  funext (cut_eq_scale n)

lemma cut_le_one (n : ℕ) (x : Fin d → ℝ) : (cut n : (Fin d → ℝ) → ℝ) x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma exists_bound_A₀ {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (smooth hf).continuous.bounded_above_of_compact_support (cs hf)
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    simp only [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

lemma cut_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (i : Fin d) (x : Fin d → ℝ),
    |dd i (cut n : (Fin d → ℝ) → ℝ) x| ≤ C / ((n : ℝ) + 1) ∧
      |dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x| ≤ C / ((n : ℝ) + 1) := by
  have hb1 : ∀ i : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |dd i (cut 0 : (Fin d → ℝ) → ℝ) x| ≤ C :=
    fun i => exists_bound_A₀ (dd_mem (cut_mem 0) i)
  have hb2 : ∀ i : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |dd i (dd i (cut 0 : (Fin d → ℝ) → ℝ)) x| ≤ C :=
    fun i => exists_bound_A₀ (dd_mem (dd_mem (cut_mem 0) i) i)
  choose C1 hC1 hC1' using hb1
  choose C2 hC2 hC2' using hb2
  refine ⟨∑ i, (C1 i + C2 i), Finset.sum_nonneg fun i _ => add_nonneg (hC1 i) (hC2 i), ?_⟩
  intro n i x
  have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hR0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hi : C1 i + C2 i ≤ ∑ j, (C1 j + C2 j) :=
    Finset.single_le_sum (f := fun j => C1 j + C2 j) (fun j _ => add_nonneg (hC1 j) (hC2 j))
      (Finset.mem_univ i)
  have e1 : dd i (cut n : (Fin d → ℝ) → ℝ) x =
      ((n : ℝ) + 1)⁻¹ * dd i (cut 0 : (Fin d → ℝ) → ℝ) (((n : ℝ) + 1)⁻¹ • x) := by
    rw [cut_eq_scale' n]; exact dd_scale (cut_smooth 0) _ i x
  have e2 : dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x =
      ((n : ℝ) + 1)⁻¹ ^ 2 * dd i (dd i (cut 0 : (Fin d → ℝ) → ℝ)) (((n : ℝ) + 1)⁻¹ • x) := by
    rw [cut_eq_scale' n]; exact dd_dd_scale (cut_smooth 0) _ i x
  have hinv : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hinv0 : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  constructor
  · rw [e1, abs_mul, abs_of_nonneg hinv0]
    calc _ ≤ ((n : ℝ) + 1)⁻¹ * C1 i :=
          mul_le_mul_of_nonneg_left (hC1' i _) hinv0
      _ ≤ ((n : ℝ) + 1)⁻¹ * ∑ j, (C1 j + C2 j) :=
          mul_le_mul_of_nonneg_left (by linarith [hC2 i]) hinv0
      _ = _ := by rw [div_eq_inv_mul]
  · rw [e2, abs_mul, abs_of_nonneg (by positivity)]
    calc _ ≤ ((n : ℝ) + 1)⁻¹ ^ 2 * C2 i :=
          mul_le_mul_of_nonneg_left (hC2' i _) (by positivity)
      _ ≤ ((n : ℝ) + 1)⁻¹ * C2 i := by
          refine mul_le_mul_of_nonneg_right ?_ (hC2 i)
          nlinarith
      _ ≤ ((n : ℝ) + 1)⁻¹ * ∑ j, (C1 j + C2 j) :=
          mul_le_mul_of_nonneg_left (by linarith [hC1 i]) hinv0
      _ = _ := by rw [div_eq_inv_mul]

lemma tendsto_div_succ (C : ℝ) : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  rw [mul_zero] at this
  exact this.congr fun n => by rw [mul_one_div]

/-! ### Graph convergence of the cut-offs -/

lemma memLp_mul_bdd {m w : (Fin d → ℝ) → ℝ} (hm : Continuous m) {c : ℝ} (hc : ∀ x, |m x| ≤ c)
    (hw : MemLp w 2 volume) : MemLp (fun x => m x * w x) 2 volume :=
  hw.of_le_mul (c := c) (hm.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hc x) (abs_nonneg _))

lemma toLp_sub_eq {f g k : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hk : MemLp k 2 volume) (h : ∀ x, f x - g x = k x) :
    hf.toLp f - hg.toLp g = hk.toLp k := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp,
    hk.coeFn_toLp] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4, h]

lemma a_mem_cut {u : (Fin d → ℝ) → ℝ} (hu : Sm u) (n : ℕ) : cut n * u ∈ A₀ d :=
  mem_A₀.2 ⟨(cut_smooth n).mul hu, (cut_cs n).mul_right⟩

lemma cut_sub_one_bound (n : ℕ) (x : Fin d → ℝ) : |(cut n : (Fin d → ℝ) → ℝ) x - 1| ≤ 1 := by
  have h1 := cut_nonneg (d := d) n x
  have h2 := cut_le_one (d := d) n x
  rw [abs_le]; constructor <;> linarith

theorem cutoff_tendsto_Rd {u : (Fin d → ℝ) → ℝ} (hu : Sm u) (h0 : MemLp u 2 volume)
    (h1 : ∀ i, MemLp (dd i u) 2 volume) (h2 : MemLp (Lf u) 2 volume)
    (hm : ∀ n : ℕ, MemLp (cut n * u) 2 volume)
    (hm2 : ∀ n : ℕ, MemLp (Lf (cut n * u)) 2 volume) :
    Tendsto (fun n : ℕ => (hm n).toLp (cut n * u)) atTop (𝓝 (h0.toLp u)) ∧
      Tendsto (fun n : ℕ => (hm2 n).toLp (Lf (cut n * u))) atTop (𝓝 (h2.toLp (Lf u))) := by
  obtain ⟨C, hC0, hC⟩ := cut_bounds (d := d)
  have hcont : ∀ n, Continuous (fun x : Fin d → ℝ => (cut n : (Fin d → ℝ) → ℝ) x - 1) := fun n =>
    (cut_smooth n).continuous.sub continuous_const
  have hlim1 : ∀ x : Fin d → ℝ, Tendsto (fun n => (cut n : (Fin d → ℝ) → ℝ) x - 1) atTop (𝓝 0) :=
    fun x => by simpa using (cut_tendsto x).sub_const 1
  have hmw1 : ∀ n, MemLp (fun x => ((cut n : (Fin d → ℝ) → ℝ) x - 1) * u x) 2 volume := fun n =>
    memLp_mul_bdd (hcont n) (cut_sub_one_bound n) h0
  constructor
  · rw [← tendsto_sub_nhds_zero_iff]
    refine (tendsto_toLp_mul_zero hcont (c := 1) cut_sub_one_bound hlim1 h0 hmw1).congr fun n => ?_
    symm
    exact toLp_sub_eq (hm n) h0 (hmw1 n) fun x => by simp only [Pi.mul_apply]; ring
  · rw [← tendsto_sub_nhds_zero_iff]
    -- the three types of multipliers
    have hmwA : ∀ n, MemLp (fun x => ((cut n : (Fin d → ℝ) → ℝ) x - 1) * Lf u x) 2 volume := fun n =>
      memLp_mul_bdd (hcont n) (cut_sub_one_bound n) h2
    have hcB : ∀ (i : Fin d) n, Continuous (fun x : Fin d → ℝ => 2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) :=
      fun i n => continuous_const.mul ((cut_smooth n).dd i).continuous
    have hbB : ∀ (i : Fin d) n x, |2 * dd i (cut n : (Fin d → ℝ) → ℝ) x| ≤ 2 * C := by
      intro i n x
      have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [abs_mul, abs_two]
      have := (hC n i x).1
      have h3 : C / ((n : ℝ) + 1) ≤ C := div_le_self hC0 hR
      linarith
    have hlimB : ∀ (i : Fin d) (x : Fin d → ℝ),
        Tendsto (fun n => 2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) atTop (𝓝 0) := by
      intro i x
      have : Tendsto (fun n => dd i (cut n : (Fin d → ℝ) → ℝ) x) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using (hC n i x).1)
          (tendsto_div_succ C)
      simpa using this.const_mul 2
    have hmwB : ∀ (i : Fin d) n, MemLp (fun x => (2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) * dd i u x) 2
        volume := fun i n => memLp_mul_bdd (hcB i n) (hbB i n) (h1 i)
    have hcC : ∀ n, Continuous (fun x : Fin d → ℝ => Lf (cut n : (Fin d → ℝ) → ℝ) x) := fun n => by
      have : (fun x : Fin d → ℝ => Lf (cut n : (Fin d → ℝ) → ℝ) x) =
          fun x => ∑ i, dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x := rfl
      rw [this]
      exact continuous_finsetSum _ fun i _ => (((cut_smooth n).dd i).dd i).continuous
    have hbC : ∀ n x, |Lf (cut n : (Fin d → ℝ) → ℝ) x| ≤ d * C := by
      intro n x
      have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h3 : C / ((n : ℝ) + 1) ≤ C := div_le_self hC0 hR
      calc |Lf (cut n : (Fin d → ℝ) → ℝ) x| ≤ ∑ i, |dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin d, C := Finset.sum_le_sum fun i _ => (hC n i x).2.trans h3
        _ = d * C := by simp
    have hlimC : ∀ x : Fin d → ℝ, Tendsto (fun n => Lf (cut n : (Fin d → ℝ) → ℝ) x) atTop (𝓝 0) := by
      intro x
      refine squeeze_zero_norm (fun n => ?_) (tendsto_div_succ (d * C))
      have : ‖Lf (cut n : (Fin d → ℝ) → ℝ) x‖ ≤ ∑ i, |dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x| :=
        Finset.abs_sum_le_sum_abs _ _
      refine this.trans ?_
      calc _ ≤ ∑ _i : Fin d, C / ((n : ℝ) + 1) := Finset.sum_le_sum fun i _ => (hC n i x).2
        _ = _ := by simp; ring
    have hmwC : ∀ n, MemLp (fun x => Lf (cut n : (Fin d → ℝ) → ℝ) x * u x) 2 volume := fun n =>
      memLp_mul_bdd (hcC n) (hbC n) h0
    have TA := tendsto_toLp_mul_zero hcont (c := 1) cut_sub_one_bound hlim1 h2 hmwA
    have TB : ∀ i : Fin d, Tendsto (fun n => (hmwB i n).toLp
        (fun x => (2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) * dd i u x)) atTop (𝓝 0) := fun i =>
      tendsto_toLp_mul_zero (hcB i) (c := 2 * C) (hbB i) (hlimB i) (h1 i) (hmwB i)
    have TC := tendsto_toLp_mul_zero hcC (c := d * C) hbC hlimC h0 hmwC
    have Tsum := (TA.add (tendsto_finsetSum Finset.univ fun i _ => TB i)).add TC
    simp only [add_zero, Finset.sum_const_zero] at Tsum
    refine Tsum.congr fun n => ?_
    symm
    refine Lp.ext ?_
    have hae : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∀ i : Fin d, ((hmwB i n).toLp
        (fun x => (2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) * dd i u x) : (Fin d → ℝ) → ℝ) x =
        (2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) * dd i u x :=
      ae_all_iff.2 fun i => (hmwB i n).coeFn_toLp
    filter_upwards [Lp.coeFn_sub ((hm2 n).toLp (Lf (cut n * u))) (h2.toLp (Lf u)),
      (hm2 n).coeFn_toLp, h2.coeFn_toLp,
      Lp.coeFn_add ((hmwA n).toLp (fun x => ((cut n : (Fin d → ℝ) → ℝ) x - 1) * Lf u x) +
        ∑ i, (hmwB i n).toLp (fun x => (2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) * dd i u x))
        ((hmwC n).toLp (fun x => Lf (cut n : (Fin d → ℝ) → ℝ) x * u x)),
      Lp.coeFn_add ((hmwA n).toLp (fun x => ((cut n : (Fin d → ℝ) → ℝ) x - 1) * Lf u x))
        (∑ i, (hmwB i n).toLp (fun x => (2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) * dd i u x)),
      coeFn_finset_sum Finset.univ (fun i => (hmwB i n).toLp
        (fun x => (2 * dd i (cut n : (Fin d → ℝ) → ℝ) x) * dd i u x)),
      (hmwA n).coeFn_toLp, (hmwC n).coeFn_toLp, hae] with x e1 e2 e3 e4 e5 e6 e7 e8 e9
    rw [e1, Pi.sub_apply, e2, e3, e4, Pi.add_apply, e5, Pi.add_apply, e6, e7, e8]
    rw [Finset.sum_congr rfl fun i _ => e9 i]
    rw [Lf_mul (cut_smooth n) hu x]
    simp only [Gf, Finset.mul_sum]
    have : ∀ i : Fin d, 2 * (dd i (cut n : (Fin d → ℝ) → ℝ) x * dd i u x) =
        2 * dd i (cut n : (Fin d → ℝ) → ℝ) x * dd i u x := fun i => by ring
    simp only [this]
    ring

end MarkovTriple.BGL.LebesgueRd
