import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Gamma2

/-!
# Cut-off approximation in `L²(ℝ^d)` (Round 24, stream A, part B-b)

If `u` is smooth with `u, ∂ᵢu, Δu ∈ L²`, the compactly supported smooth functions `ζ_n u`
(`ζ_n = cut n = Θ(x/(n+1))`) converge to `u` in `L²` and `Δ(ζ_n u) → Δu` in `L²`
(`cutoff_graph`).  Port of `Instances/Lebesgue/Cutoff.lean` to `ℝ^d`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

/-- `‖[g]‖² = ∫ g²`. -/
lemma norm_toLp_sq_E {g : (Fin d → ℝ) → ℝ} (hg : MemLp g 2 volume) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, (g x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]
  simp

lemma tendsto_toLp_of_integral_sq' {G : ℕ → (Fin d → ℝ) → ℝ} {F : (Fin d → ℝ) → ℝ}
    (hG : ∀ n, MemLp (G n) 2 volume) (hF : MemLp F 2 volume)
    (h : Tendsto (fun n => ∫ x, (G n x - F x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 (hF.toLp F)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ n, ‖(hG n).toLp (G n) - hF.toLp F‖ = Real.sqrt (∫ x, (G n x - F x) ^ 2) := by
    intro n
    have hd : MemLp (fun x => G n x - F x) 2 volume := (hG n).sub hF
    have h1 : (hG n).toLp (G n) - hF.toLp F = hd.toLp (fun x => G n x - F x) := by
      rw [← MemLp.toLp_sub]; rfl
    rw [h1, ← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq_E hd]
  simp only [e]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  exact this

/-- `m` bounded measurable, `w ∈ L²`. -/
lemma sq_mul_integrable' {m w : (Fin d → ℝ) → ℝ} (hm : Measurable m) {c : ℝ} (hc : ∀ x, |m x| ≤ c)
    (hw : MemLp w 2 volume) : Integrable (fun x => (m x * w x) ^ 2) ∧
      ∫ x, (m x * w x) ^ 2 ≤ c ^ 2 * ∫ x, (w x) ^ 2 := by
  have hw2 : Integrable (fun x => (w x) ^ 2) := hw.integrable_sq
  have hle : ∀ x, (m x * w x) ^ 2 ≤ c ^ 2 * (w x) ^ 2 := by
    intro x
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hc x, abs_nonneg (m x), sq_abs (m x)])
      (sq_nonneg _)
  have hint : Integrable (fun x => (m x * w x) ^ 2) := by
    refine Integrable.mono' (hw2.const_mul (c ^ 2)) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hm.aestronglyMeasurable.mul hw.aestronglyMeasurable).pow 2)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle x
  exact ⟨hint, by
    calc ∫ x, (m x * w x) ^ 2 ≤ ∫ x, c ^ 2 * (w x) ^ 2 :=
          integral_mono hint (hw2.const_mul _) hle
      _ = c ^ 2 * ∫ x, (w x) ^ 2 := integral_const_mul _ _⟩

/-! ### Scaling of the profile -/

lemma dd_scale_E {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (c : ℝ) (i : Fin d) :
    dd i (fun x => f (c • x)) = fun x => c * dd i f (c • x) := by
  funext x
  unfold dd
  have h1 : HasFDerivAt (fun x : Fin d → ℝ => f (c • x))
      ((fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ (Fin d → ℝ))) x :=
    (hasFDerivAt_of hf (c • x)).comp x ((hasFDerivAt_id x).const_smul c)
  rw [h1.fderiv]
  simp

lemma dd_const_mul {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (c : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    dd i (fun x => c * f x) x = c * dd i f x := by
  have := congrFun (dd_smul c hf i) x
  exact this

lemma sq_smul_E (c : ℝ) (x : Fin d → ℝ) : sq (c • x) = c ^ 2 * sq x := by
  unfold sq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_pow]

lemma cut_eq_scale_E (n : ℕ) :
    (cut n : (Fin d → ℝ) → ℝ) = fun x => (cut 0 : (Fin d → ℝ) → ℝ) ((((n : ℝ) + 1)⁻¹) • x) := by
  funext x
  unfold cut
  rw [sq_smul_E]
  simp [div_eq_mul_inv, mul_comm, inv_pow]

lemma dd_cut (n : ℕ) (i : Fin d) (x : Fin d → ℝ) :
    dd i (cut n : (Fin d → ℝ) → ℝ) x = ((n : ℝ) + 1)⁻¹ * dd i (cut 0 : (Fin d → ℝ) → ℝ) ((((n : ℝ) + 1)⁻¹) • x) := by
  rw [cut_eq_scale_E n, dd_scale_E (cut_smooth 0)]

lemma dd_dd_cut (n : ℕ) (i : Fin d) (x : Fin d → ℝ) :
    dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x =
      ((n : ℝ) + 1)⁻¹ ^ 2 * dd i (dd i (cut 0 : (Fin d → ℝ) → ℝ)) ((((n : ℝ) + 1)⁻¹) • x) := by
  have e : dd i (cut n : (Fin d → ℝ) → ℝ) =
      fun x => ((n : ℝ) + 1)⁻¹ * dd i (cut 0 : (Fin d → ℝ) → ℝ) ((((n : ℝ) + 1)⁻¹) • x) :=
    funext (dd_cut n i)
  rw [e, dd_const_mul (f := fun x => dd i (cut 0 : (Fin d → ℝ) → ℝ) ((((n : ℝ) + 1)⁻¹) • x))
    (((cut_smooth 0).dd i).comp (contDiff_const_smul _)) , dd_scale_E ((cut_smooth 0).dd i)]
  ring

lemma bound_of_A₀ {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (smooth hf).continuous.bounded_above_of_compact_support (cs hf)
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    simp only [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

lemma cut0_bounds : ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧
    (∀ i x, |dd i (cut 0 : (Fin d → ℝ) → ℝ) x| ≤ C1) ∧
    (∀ i x, |dd i (dd i (cut 0 : (Fin d → ℝ) → ℝ)) x| ≤ C2) := by
  have h1 : ∀ i : Fin d, ∃ C, 0 ≤ C ∧ ∀ x, |dd i (cut 0 : (Fin d → ℝ) → ℝ) x| ≤ C :=
    fun i => bound_of_A₀ (dd_mem (cut_mem 0) i)
  have h2 : ∀ i : Fin d, ∃ C, 0 ≤ C ∧ ∀ x, |dd i (dd i (cut 0 : (Fin d → ℝ) → ℝ)) x| ≤ C :=
    fun i => bound_of_A₀ (dd_mem (dd_mem (cut_mem 0) i) i)
  choose C1 hC1 hC1' using h1
  choose C2 hC2 hC2' using h2
  refine ⟨∑ i, C1 i, ∑ i, C2 i, Finset.sum_nonneg fun i _ => hC1 i, Finset.sum_nonneg fun i _ => hC2 i,
    fun i x => (hC1' i x).trans ?_, fun i x => (hC2' i x).trans ?_⟩
  · exact Finset.single_le_sum (f := C1) (fun j _ => hC1 j) (Finset.mem_univ i)
  · exact Finset.single_le_sum (f := C2) (fun j _ => hC2 j) (Finset.mem_univ i)

/-- the scale `R n = n + 1`. -/
noncomputable def Rn (n : ℕ) : ℝ := (n : ℝ) + 1

lemma Rn_pos (n : ℕ) : 0 < Rn n := by unfold Rn; positivity

lemma cut_le_one' (n : ℕ) (x : Fin d → ℝ) : cut n x ≤ 1 := Real.smoothTransition.le_one _

lemma abs_cut_sub_one_le (n : ℕ) (x : Fin d → ℝ) : |cut n x - 1| ≤ 1 := by
  have h1 := cut_nonneg n x
  have h2 := cut_le_one' n x
  rw [abs_le]; constructor <;> linarith

lemma tendsto_integral_sq_cut {w : (Fin d → ℝ) → ℝ} (hw : MemLp w 2 volume) :
    Tendsto (fun n : ℕ => ∫ x, ((cut n x - 1) * w x) ^ 2) atTop (𝓝 0) := by
  have hw2 : Integrable (fun x => (w x) ^ 2) := hw.integrable_sq
  have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Fin d → ℝ)))
    (F := fun (n : ℕ) x => ((cut n x - 1) * w x) ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => (w x) ^ 2)
    (fun n => ((((cut_smooth n).continuous.sub continuous_const).aestronglyMeasurable).mul
      hw.aestronglyMeasurable).pow 2)
    hw2
    (fun n => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (by
        have := abs_cut_sub_one_le n x
        nlinarith [sq_abs (cut n x - 1), abs_nonneg (cut n x - 1)]))
    (Filter.Eventually.of_forall fun x => by
      have h := ((cut_tendsto x).sub_const 1).mul_const (w x) |>.pow 2
      simpa using h)
  simpa using this

lemma Lf_cut_mul_sub {u : (Fin d → ℝ) → ℝ} (hu : Sm u) (n : ℕ) (x : Fin d → ℝ) :
    Lf (cut n * u) x - Lf u x =
      (cut n x - 1) * Lf u x + 2 * Gf (cut n) u x + Lf (cut n) x * u x := by
  rw [Lf_mul (cut_smooth n) hu x]; ring

lemma abs_dd_cut_le {C1 : ℝ} (hC1 : ∀ i x, |dd i (cut 0 : (Fin d → ℝ) → ℝ) x| ≤ C1) (n : ℕ)
    (i : Fin d) (x : Fin d → ℝ) : |dd i (cut n : (Fin d → ℝ) → ℝ) x| ≤ C1 * (1 / ((n : ℝ) + 1)) := by
  rw [dd_cut, abs_mul, abs_of_pos (by positivity : (0:ℝ) < ((n : ℝ) + 1)⁻¹), mul_comm, one_div]
  exact mul_le_mul_of_nonneg_right (hC1 i _) (by positivity)

lemma abs_Lf_cut_le {C2 : ℝ} (hC2 : ∀ i x, |dd i (dd i (cut 0 : (Fin d → ℝ) → ℝ)) x| ≤ C2) (n : ℕ)
    (x : Fin d → ℝ) : |Lf (cut n : (Fin d → ℝ) → ℝ) x| ≤ (d * C2) * (1 / ((n : ℝ) + 1)) ^ 2 := by
  have hpos : (0:ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have h1 : ∀ i, |dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x| ≤ C2 * (1 / ((n : ℝ) + 1)) ^ 2 := by
    intro i
    rw [dd_dd_cut, abs_mul, abs_of_pos (pow_pos hpos 2), mul_comm, one_div]
    exact mul_le_mul_of_nonneg_right (hC2 i _) (by positivity)
  calc |Lf (cut n : (Fin d → ℝ) → ℝ) x| = |∑ i, dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x| := rfl
    _ ≤ ∑ i, |dd i (dd i (cut n : (Fin d → ℝ) → ℝ)) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, C2 * (1 / ((n : ℝ) + 1)) ^ 2 := Finset.sum_le_sum fun i _ => h1 i
    _ = (d * C2) * (1 / ((n : ℝ) + 1)) ^ 2 := by simp; ring

lemma abs_Gf_cut_le {C1 : ℝ} (hC1 : ∀ i x, |dd i (cut 0 : (Fin d → ℝ) → ℝ) x| ≤ C1) (n : ℕ)
    (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    |Gf (cut n) u x| ≤ (C1 * (1 / ((n : ℝ) + 1))) * ∑ i, ‖dd i u x‖ := by
  calc |Gf (cut n) u x| = |∑ i, dd i (cut n) x * dd i u x| := rfl
    _ ≤ ∑ i, |dd i (cut n) x * dd i u x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (C1 * (1 / ((n : ℝ) + 1))) * ‖dd i u x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_dd_cut_le hC1 n i x) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

lemma cutoff_graph_aux {u : (Fin d → ℝ) → ℝ} (hu : Sm u) (h0 : MemLp u 2 volume)
    (h1 : ∀ i, MemLp (dd i u) 2 volume) (h2 : MemLp (Lf u) 2 volume) :
    Tendsto (fun n : ℕ => ∫ x, (Lf (cut n * u) x - Lf u x) ^ 2) atTop (𝓝 0) := by
  obtain ⟨C1, C2, hC1n, hC2n, hC1, hC2⟩ := cut0_bounds (d := d)
  set W : (Fin d → ℝ) → ℝ := fun x => ∑ i, ‖dd i u x‖ with hW
  have hWL : MemLp W 2 volume := memLp_finsetSum _ fun i _ => (h1 i).norm
  have hW2 : Integrable (fun x => (W x) ^ 2) := hWL.integrable_sq
  have hu2 : Integrable (fun x => (u x) ^ 2) := h0.integrable_sq
  set k1 : ℕ → ℝ := fun n => 2 * C1 * (1 / ((n : ℝ) + 1)) with hk1
  set k2 : ℕ → ℝ := fun n => (d * C2) * (1 / ((n : ℝ) + 1)) ^ 2 with hk2
  have hk1n : ∀ n, 0 ≤ k1 n := fun n => by positivity
  have hk2n : ∀ n, 0 ≤ k2 n := fun n => by positivity
  have hmA : ∀ n, Measurable (fun x : Fin d → ℝ => cut n x - 1) := fun n =>
    ((cut_smooth n).continuous.sub continuous_const).measurable
  have hAint : ∀ n, Integrable (fun x => ((cut n x - 1) * Lf u x) ^ 2) :=
    fun n => (sq_mul_integrable' (hmA n) (abs_cut_sub_one_le n) h2).1
  have hBint : ∀ n, Integrable (fun x => (k1 n * W x) ^ 2) ∧
      ∫ x, (k1 n * W x) ^ 2 ≤ (k1 n) ^ 2 * ∫ x, (W x) ^ 2 := fun n =>
    sq_mul_integrable' (m := fun _ => k1 n) measurable_const (c := k1 n)
      (fun x => (abs_of_nonneg (hk1n n)).le) hWL
  have hCint : ∀ n, Integrable (fun x => (k2 n * u x) ^ 2) ∧
      ∫ x, (k2 n * u x) ^ 2 ≤ (k2 n) ^ 2 * ∫ x, (u x) ^ 2 := fun n =>
    sq_mul_integrable' (m := fun _ => k2 n) measurable_const (c := k2 n)
      (fun x => (abs_of_nonneg (hk2n n)).le) h0
  set bnd : ℕ → ℝ := fun n => 3 * ((∫ x, ((cut n x - 1) * Lf u x) ^ 2) +
      (k1 n) ^ 2 * (∫ x, (W x) ^ 2) + (k2 n) ^ 2 * (∫ x, (u x) ^ 2)) with hbnd
  have hr : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hbnd0 : Tendsto bnd atTop (𝓝 0) := by
    have hr1 : Tendsto (fun n => (k1 n) ^ 2) atTop (𝓝 0) := by
      have h := (hr.const_mul (2 * C1)).pow 2
      rw [mul_zero, zero_pow two_ne_zero] at h
      exact h
    have hr2 : Tendsto (fun n => (k2 n) ^ 2) atTop (𝓝 0) := by
      have h := ((hr.pow 2).const_mul ((d : ℝ) * C2)).pow 2
      rw [zero_pow two_ne_zero, mul_zero, zero_pow two_ne_zero] at h
      exact h
    have := ((tendsto_integral_sq_cut h2).add (hr1.mul_const (∫ x, (W x) ^ 2))).add
      (hr2.mul_const (∫ x, (u x) ^ 2))
    have h3 := this.const_mul 3
    simp only [zero_mul, add_zero, mul_zero] at h3
    exact h3
  refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hbnd0
  have hsum : Integrable (fun x => 3 * (((cut n x - 1) * Lf u x) ^ 2 + (k1 n * W x) ^ 2 +
      (k2 n * u x) ^ 2)) :=
    ((hAint n).add (hBint n).1 |>.add (hCint n).1).const_mul 3
  calc ∫ x, (Lf (cut n * u) x - Lf u x) ^ 2
      ≤ ∫ x, 3 * (((cut n x - 1) * Lf u x) ^ 2 + (k1 n * W x) ^ 2 + (k2 n * u x) ^ 2) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hsum
          (Filter.Eventually.of_forall fun x => ?_)
        beta_reduce
        rw [Lf_cut_mul_sub hu n x]
        have hb : (2 * Gf (cut n) u x) ^ 2 ≤ (k1 n * W x) ^ 2 := by
          have := abs_Gf_cut_le hC1 n u x
          have e : |2 * Gf (cut n) u x| ≤ k1 n * W x := by
            rw [abs_mul, abs_two, hk1, hW]
            nlinarith
          calc (2 * Gf (cut n) u x) ^ 2 = |2 * Gf (cut n) u x| ^ 2 := (sq_abs _).symm
            _ ≤ (k1 n * W x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) e 2
        have hc : (Lf (cut n) x * u x) ^ 2 ≤ (k2 n * u x) ^ 2 := by
          have e : |Lf (cut n) x * u x| ≤ k2 n * |u x| := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (abs_Lf_cut_le hC2 n x) (abs_nonneg _)
          calc (Lf (cut n) x * u x) ^ 2 = |Lf (cut n) x * u x| ^ 2 := (sq_abs _).symm
            _ ≤ (k2 n * |u x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) e 2
            _ = (k2 n * u x) ^ 2 := by simp only [mul_pow, sq_abs]
        nlinarith [sq_nonneg ((cut n x - 1) * Lf u x - 2 * Gf (cut n) u x),
          sq_nonneg ((cut n x - 1) * Lf u x - Lf (cut n) x * u x),
          sq_nonneg (2 * Gf (cut n) u x - Lf (cut n) x * u x)]
    _ = 3 * ((∫ x, ((cut n x - 1) * Lf u x) ^ 2) + (∫ x, (k1 n * W x) ^ 2) +
          (∫ x, (k2 n * u x) ^ 2)) := by
        have hAB : Integrable (fun x => ((cut n x - 1) * Lf u x) ^ 2 + (k1 n * W x) ^ 2) :=
          (hAint n).add (hBint n).1
        rw [integral_const_mul, integral_add hAB (hCint n).1, integral_add (hAint n) (hBint n).1]
    _ ≤ bnd n := by
        rw [hbnd]
        have := (hBint n).2
        have := (hCint n).2
        linarith

theorem cutoff_graph {u : (Fin d → ℝ) → ℝ} (hu : Sm u) (h0 : MemLp u 2 volume)
    (h1 : ∀ i, MemLp (dd i u) 2 volume) (h2 : MemLp (Lf u) 2 volume)
    (hm : ∀ n : ℕ, MemLp (cut n * u) 2 volume)
    (hm2 : ∀ n : ℕ, MemLp (Lf (cut n * u)) 2 volume) :
    Tendsto (fun n : ℕ => (hm n).toLp (cut n * u)) atTop (𝓝 (h0.toLp u)) ∧
      Tendsto (fun n : ℕ => (hm2 n).toLp (Lf (cut n * u))) atTop (𝓝 (h2.toLp (Lf u))) := by
  refine ⟨tendsto_toLp_of_integral_sq' hm h0 ?_, tendsto_toLp_of_integral_sq' hm2 h2
    (cutoff_graph_aux hu h0 h1 h2)⟩
  refine (tendsto_integral_sq_cut h0).congr (fun n => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]
  ring

end MarkovTriple.BGL.LebesgueRd
