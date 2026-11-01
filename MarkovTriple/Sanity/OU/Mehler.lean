import MarkovTriple.Sanity.OU.Full

/-! # OU (Part 16): the Mehler transform `Mh a c f (x) = ∫ f (a x + c y) dγ(y)` of a test function

For `f ∈ C_c^∞(ℝ)` and `a > 0`: `Mh a c f` is smooth, `(Mh a c f)^{(n)} = aⁿ Mh a c (f^{(n)})`, and it
has Gaussian-tail (here: faster than any polynomial) decay.  Hence it is a Schwartz function
(`mehlerS`). -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Real SchwartzMap

namespace MarkovTriple.Sanity.OU

/-- the Mehler transform -/
noncomputable def Mh (a c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, f (a * x + c * y) ∂γ

lemma A₀.bdd {f : ℝ → ℝ} (hf : f ∈ A₀) : ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  exact ⟨C, fun x => by simpa using hC x⟩

lemma A₀.iteratedDeriv_mem (n : ℕ) : ∀ {f : ℝ → ℝ}, f ∈ A₀ → iteratedDeriv n f ∈ A₀ := by
  induction n with
  | zero => intro f hf; simpa using hf
  | succ n ih => intro f hf; rw [iteratedDeriv_succ']; exact ih (A₀.deriv_mem hf)

lemma integrable_comp_mh {f : ℝ → ℝ} (hf : f ∈ A₀) (a c x : ℝ) :
    Integrable (fun y => f (a * x + c * y)) γ := by
  obtain ⟨C, hC⟩ := A₀.bdd hf
  refine Integrable.of_bound (C := C) ?_ (ae_of_all _ fun y => ?_)
  · exact (hf.1.continuous.comp (by fun_prop)).aestronglyMeasurable
  · simpa using hC _

lemma hasDerivAt_Mh {f : ℝ → ℝ} (hf : f ∈ A₀) (a c x : ℝ) :
    HasDerivAt (Mh a c f) (a * Mh a c (deriv f) x) x := by
  obtain ⟨C, hC⟩ := A₀.bdd (A₀.deriv_mem hf)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ)
    (F := fun x y => f (a * x + c * y)) (F' := fun x y => a * deriv f (a * x + c * y))
    (x₀ := x) (s := Set.univ) (bound := fun _ => |a| * C) Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (hf.1.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_mh hf a c x)
    ((continuous_const.mul ((A₀.deriv_mem hf).1.continuous.comp (by fun_prop))).aestronglyMeasurable)
    (ae_of_all _ fun y z _ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _))
    (integrable_const _)
    (ae_of_all _ fun y z _ => by
      have h1 : HasDerivAt (fun x => a * x + c * y) a z := by
        simpa using ((hasDerivAt_id z).const_mul a).add_const (c * y)
      have h2 := (hf.1.hasDerivAt (a * z + c * y)).comp z h1
      exact (show HasDerivAt (fun x => f (a * x + c * y)) (deriv f (a * z + c * y) * a) z from h2
        ).congr_deriv (mul_comm _ _))
  have := hd.2
  rw [integral_const_mul] at this
  exact this

lemma deriv_Mh {f : ℝ → ℝ} (hf : f ∈ A₀) (a c : ℝ) :
    deriv (Mh a c f) = fun x => a * Mh a c (deriv f) x :=
  funext fun x => (hasDerivAt_Mh hf a c x).deriv

lemma contDiff_Mh (a c : ℝ) : ∀ (n : ℕ) {f : ℝ → ℝ}, f ∈ A₀ → ContDiff ℝ n (Mh a c f) := by
  intro n
  induction n with
  | zero =>
    intro f hf
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x => (hasDerivAt_Mh hf a c x).continuousAt)
  | succ n ih =>
    intro f hf
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_Mh hf a c x).differentiableAt, by simp, ?_⟩
    rw [deriv_Mh hf]
    exact contDiff_const.mul (ih (A₀.deriv_mem hf))

lemma sm_Mh (a c : ℝ) {f : ℝ → ℝ} (hf : f ∈ A₀) : Sm (Mh a c f) :=
  contDiff_infty.2 fun n => contDiff_Mh a c n hf

lemma iteratedDeriv_Mh (a c : ℝ) : ∀ (n : ℕ) {f : ℝ → ℝ}, f ∈ A₀ →
    iteratedDeriv n (Mh a c f) = fun x => a ^ n * Mh a c (iteratedDeriv n f) x := by
  intro n
  induction n with
  | zero => intro f hf; simp
  | succ n ih =>
    intro f hf
    rw [iteratedDeriv_succ', deriv_Mh hf, iteratedDeriv_succ']
    funext x
    rw [iteratedDeriv_const_mul_field, ih (A₀.deriv_mem hf)]
    ring

/-- decay faster than any polynomial -/
lemma decay_Mh {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 1) {f : ℝ → ℝ} (hf : f ∈ A₀) (m : ℕ) :
    ∃ C, ∀ x, |x| ^ m * |Mh a c f x| ≤ C := by
  obtain ⟨B, hB⟩ := A₀.bdd hf
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z, R < |z| → f z = 0 := by
    obtain ⟨R, hR⟩ := hf.2.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨R, fun z hz => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
    have := hR h
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  have key : ∀ x y : ℝ, |x| ^ m * |f (a * x + c * y)| ≤
      B * (((|R| + 1) / a) ^ m * (1 + |y|) ^ m) := by
    intro x y
    by_cases h : R < |a * x + c * y|
    · rw [hR _ h]; simp only [abs_zero, mul_zero]; positivity
    · replace h := not_lt.1 h
      have h1 : a * |x| ≤ (|R| + 1) * (1 + |y|) := by
        have e1 : |a * x| ≤ |a * x + c * y| + |c * y| := by
          simpa using abs_sub (a * x + c * y) (c * y)
        have e2 : |c * y| ≤ |y| := by
          rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hc
        rw [abs_mul, abs_of_pos ha] at e1
        have := le_abs_self R
        nlinarith [abs_nonneg y, abs_nonneg R]
      have h2 : |x| ≤ (|R| + 1) / a * (1 + |y|) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ ha]; linarith
      calc |x| ^ m * |f (a * x + c * y)| ≤ ((|R| + 1) / a * (1 + |y|)) ^ m * B :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h2 m) (hB _) (abs_nonneg _) (by positivity)
        _ = _ := by rw [mul_pow]; ring
  refine ⟨B * (((|R| + 1) / a) ^ m * ∫ y, (1 + |y|) ^ m ∂γ), fun x => ?_⟩
  have hint : Integrable (fun y : ℝ => B * (((|R| + 1) / a) ^ m * (1 + |y|) ^ m)) γ :=
    ((integrable_one_add_abs_pow m).const_mul _).const_mul _
  calc |x| ^ m * |Mh a c f x| = ‖∫ y, |x| ^ m * f (a * x + c * y) ∂γ‖ := by
        rw [integral_const_mul, Real.norm_eq_abs, abs_mul, abs_pow, abs_abs]; rfl
    _ ≤ ∫ y, ‖|x| ^ m * f (a * x + c * y)‖ ∂γ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * (((|R| + 1) / a) ^ m * (1 + |y|) ^ m) ∂γ := by
        refine integral_mono ((integrable_comp_mh hf a c x).const_mul _).norm hint fun y => ?_
        simpa [abs_mul] using key x y
    _ = _ := by rw [integral_const_mul, integral_const_mul]

/-- the Mehler transform of a test function is a Schwartz function -/
noncomputable def mehlerS {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 1) {f : ℝ → ℝ} (hf : f ∈ A₀) :
    𝓢(ℝ, ℝ) where
  toFun := Mh a c f
  smooth' := sm_Mh a c hf
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := decay_Mh ha c hc (A₀.iteratedDeriv_mem n hf) k
    refine ⟨a ^ n * C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_Mh a c n hf, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos ha]
    calc |x| ^ k * (a ^ n * |Mh a c (iteratedDeriv n f) x|)
        = a ^ n * (|x| ^ k * |Mh a c (iteratedDeriv n f) x|) := by ring
      _ ≤ a ^ n * C := mul_le_mul_of_nonneg_left (hC x) (by positivity)

lemma mehlerS_apply {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 1) {f : ℝ → ℝ} (hf : f ∈ A₀) :
    ⇑(mehlerS ha c hc hf) = Mh a c f := rfl

end MarkovTriple.Sanity.OU
