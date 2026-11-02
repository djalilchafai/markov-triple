import Mathlib
import MarkovTriple.BGL.Instances.OUCompact.Class
import MarkovTriple.BGL.Analysis.OU.MehlerEq

/-!
# The Mehler transform preserves `ℬ`; Mehler's formula for `f ∈ ℬ`

For `f ∈ ℬ` (`OUCompact.Bm`) and `a > 0`, `|c| ≤ 1`:
`Mh a c f (x) = ∫ f(a x + c y) dγ(y)` is again in `ℬ` (`Bm.Mh`): `(Mh f)' = a · Mh f'` and the
Mehler transform of a Schwartz function is Schwartz (`mehlerS'`; decay by Peetre's inequality
`a|x| ≤ (1 + |a x + c y|)(1 + |y|)`).  The Hermite-coefficient computation of the legacy
`coeff_Mh` only uses that `f` is continuous and bounded; it is repeated here in that generality.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real SchwartzMap InnerProductSpace
open MarkovTriple.Sanity.OU hiding A₀

namespace MarkovTriple.BGL.Instances.OUCompact

/-- smooth with all derivatives bounded -/
def Sb (f : ℝ → ℝ) : Prop := Sm f ∧ ∀ n, ∃ C, ∀ x, |iteratedDeriv n f x| ≤ C

lemma Sb.bdd {f : ℝ → ℝ} (hf : Sb f) : ∃ C, ∀ x, |f x| ≤ C := by simpa using hf.2 0

lemma Sb.deriv' {f : ℝ → ℝ} (hf : Sb f) : Sb (deriv f) :=
  ⟨hf.1.deriv', fun n => by simpa [iteratedDeriv_succ'] using hf.2 (n + 1)⟩

lemma schw_sb (W : 𝓢(ℝ, ℝ)) : Sb ⇑W := by
  refine ⟨schw_sm W, fun n => ?_⟩
  obtain ⟨D, -, hD⟩ := W.decay 0 n
  refine ⟨D, fun x => ?_⟩
  have := hD x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at this
  simpa using this

lemma Bm.sb {f : ℝ → ℝ} (hf : Bm f) : Sb f := by
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  refine ⟨hf.1, fun n => ?_⟩
  rcases n with _ | n
  · simpa using hf.bdd
  · obtain ⟨C, hC⟩ := (schw_sb W).2 n
    refine ⟨C, fun x => ?_⟩
    rw [iteratedDeriv_succ', ← hW]
    exact hC x

/-! ### The Mehler transform of a function in `Sb` -/

lemma integrable_comp_Mh {f : ℝ → ℝ} (hf : Sb f) (a c x : ℝ) :
    Integrable (fun y => f (a * x + c * y)) γ := by
  obtain ⟨C, hC⟩ := hf.bdd
  refine Integrable.of_bound (C := C) ?_ (ae_of_all _ fun y => ?_)
  · exact (hf.1.continuous.comp (by fun_prop)).aestronglyMeasurable
  · simpa using hC _

lemma hasDerivAt_Mh' {f : ℝ → ℝ} (hf : Sb f) (a c x : ℝ) :
    HasDerivAt (Mh a c f) (a * Mh a c (deriv f) x) x := by
  obtain ⟨C, hC⟩ := hf.deriv'.bdd
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ)
    (F := fun x y => f (a * x + c * y)) (F' := fun x y => a * deriv f (a * x + c * y))
    (x₀ := x) (s := Set.univ) (bound := fun _ => |a| * C) Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (hf.1.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_Mh hf a c x)
    ((continuous_const.mul (hf.deriv'.1.continuous.comp (by fun_prop))).aestronglyMeasurable)
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

lemma deriv_Mh' {f : ℝ → ℝ} (hf : Sb f) (a c : ℝ) :
    deriv (Mh a c f) = fun x => a * Mh a c (deriv f) x :=
  funext fun x => (hasDerivAt_Mh' hf a c x).deriv

lemma contDiff_Mh' (a c : ℝ) : ∀ (n : ℕ) {f : ℝ → ℝ}, Sb f → ContDiff ℝ n (Mh a c f) := by
  intro n
  induction n with
  | zero =>
    intro f hf
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x => (hasDerivAt_Mh' hf a c x).continuousAt)
  | succ n ih =>
    intro f hf
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_Mh' hf a c x).differentiableAt, by simp, ?_⟩
    rw [deriv_Mh' hf]
    exact contDiff_const.mul (ih hf.deriv')

lemma sm_Mh' (a c : ℝ) {f : ℝ → ℝ} (hf : Sb f) : Sm (Mh a c f) :=
  contDiff_infty.2 fun n => contDiff_Mh' a c n hf

lemma iteratedDeriv_Mh' (a c : ℝ) : ∀ (n : ℕ) {f : ℝ → ℝ}, Sb f →
    iteratedDeriv n (Mh a c f) = fun x => a ^ n * Mh a c (iteratedDeriv n f) x := by
  intro n
  induction n with
  | zero => intro f hf; simp
  | succ n ih =>
    intro f hf
    rw [iteratedDeriv_succ', deriv_Mh' hf, iteratedDeriv_succ']
    funext x
    rw [iteratedDeriv_const_mul_field, ih hf.deriv']
    ring

lemma abs_Mh_le {f : ℝ → ℝ} (hf : Sb f) (a c : ℝ) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (x : ℝ) :
    |Mh a c f x| ≤ C := by
  have : |Mh a c f x| ≤ ∫ y, |f (a * x + c * y)| ∂γ := by
    simpa [Mh, Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := γ)
      (fun y => f (a * x + c * y))
  refine this.trans ?_
  calc ∫ y, |f (a * x + c * y)| ∂γ ≤ ∫ _y, C ∂γ :=
        integral_mono (integrable_comp_Mh hf a c x).abs (integrable_const _) fun y => hC _
    _ = C := by simp

/-- decay of the Mehler transform of a rapidly decreasing bounded function (Peetre) -/
lemma decay_Mh' {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 1) {V : ℝ → ℝ} (hV : Sb V)
    (hd : ∀ m : ℕ, ∃ D, ∀ z, (1 + |z|) ^ m * |V z| ≤ D) (m : ℕ) :
    ∃ C, ∀ x, |x| ^ m * |Mh a c V x| ≤ C := by
  obtain ⟨D, hD⟩ := hd m
  have key : ∀ x y : ℝ, |x| ^ m * |V (a * x + c * y)| ≤ (a⁻¹) ^ m * (D * (1 + |y|) ^ m) := by
    intro x y
    set z := a * x + c * y with hz
    have h1 : a * |x| ≤ (1 + |z|) * (1 + |y|) := by
      have e1 : |a * x| ≤ |z| + |c * y| := by
        calc |a * x| = |z - c * y| := by congr 1; rw [hz]; ring
          _ ≤ |z| + |c * y| := abs_sub _ _
      have e2 : |c * y| ≤ |y| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hc
      rw [abs_mul, abs_of_pos ha] at e1
      nlinarith [abs_nonneg y, abs_nonneg z]
    have h2 : |x| ≤ a⁻¹ * ((1 + |z|) * (1 + |y|)) := by
      rw [← div_eq_inv_mul, le_div_iff₀ ha]; linarith
    have h3 : |x| ^ m ≤ (a⁻¹) ^ m * ((1 + |z|) ^ m * (1 + |y|) ^ m) := by
      calc |x| ^ m ≤ (a⁻¹ * ((1 + |z|) * (1 + |y|))) ^ m := pow_le_pow_left₀ (abs_nonneg _) h2 m
        _ = _ := by rw [mul_pow, mul_pow]
    calc |x| ^ m * |V z| ≤ ((a⁻¹) ^ m * ((1 + |z|) ^ m * (1 + |y|) ^ m)) * |V z| :=
          mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      _ = (a⁻¹) ^ m * ((1 + |y|) ^ m * ((1 + |z|) ^ m * |V z|)) := by ring
      _ ≤ (a⁻¹) ^ m * ((1 + |y|) ^ m * D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD z) (by positivity)) (by positivity)
      _ = _ := by ring
  refine ⟨(a⁻¹) ^ m * (D * ∫ y, (1 + |y|) ^ m ∂γ), fun x => ?_⟩
  have hint : Integrable (fun y : ℝ => (a⁻¹) ^ m * (D * (1 + |y|) ^ m)) γ :=
    ((integrable_one_add_abs_pow m).const_mul D).const_mul _
  calc |x| ^ m * |Mh a c V x| = ‖∫ y, |x| ^ m * V (a * x + c * y) ∂γ‖ := by
        rw [integral_const_mul, Real.norm_eq_abs, abs_mul, abs_pow, abs_abs]; rfl
    _ ≤ ∫ y, ‖|x| ^ m * V (a * x + c * y)‖ ∂γ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (a⁻¹) ^ m * (D * (1 + |y|) ^ m) ∂γ := by
        refine integral_mono ((integrable_comp_Mh hV a c x).const_mul _).norm hint fun y => ?_
        simpa [abs_mul] using key x y
    _ = _ := by rw [integral_const_mul, integral_const_mul]

lemma Sb.iter (n : ℕ) : ∀ {f : ℝ → ℝ}, Sb f → Sb (iteratedDeriv n f) := by
  induction n with
  | zero => intro f hf; simpa using hf
  | succ n ih => intro f hf; rw [iteratedDeriv_succ']; exact ih hf.deriv'

lemma schw_iter_decay (W : 𝓢(ℝ, ℝ)) (n m : ℕ) :
    ∃ D, ∀ z, (1 + |z|) ^ m * |iteratedDeriv n ⇑W z| ≤ D := by
  obtain ⟨C0, -, h0⟩ := W.decay 0 n
  obtain ⟨Cm, -, hm⟩ := W.decay m n
  refine ⟨2 ^ m * (C0 + Cm), fun z => ?_⟩
  have e0 := h0 z
  have em := hm z
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at e0 em
  simp only [Real.norm_eq_abs, pow_zero, one_mul] at e0 em
  calc (1 + |z|) ^ m * |iteratedDeriv n ⇑W z| ≤ (2 ^ m * (1 + |z| ^ m)) * |iteratedDeriv n ⇑W z| :=
        mul_le_mul_of_nonneg_right (one_add_abs_pow_le m z) (abs_nonneg _)
    _ = 2 ^ m * (|iteratedDeriv n ⇑W z| + |z| ^ m * |iteratedDeriv n ⇑W z|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add e0 em) (by positivity)

/-- the Mehler transform of a Schwartz function is a Schwartz function -/
noncomputable def mehlerS' {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 1) (W : 𝓢(ℝ, ℝ)) :
    𝓢(ℝ, ℝ) where
  toFun := Mh a c W
  smooth' := sm_Mh' a c (schw_sb W)
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := decay_Mh' ha c hc (Sb.iter n (schw_sb W)) (schw_iter_decay W n) k
    refine ⟨a ^ n * C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_Mh' a c n (schw_sb W),
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos ha]
    calc ‖x‖ ^ k * (a ^ n * |Mh a c (iteratedDeriv n ⇑W) x|)
        = a ^ n * (|x| ^ k * |Mh a c (iteratedDeriv n ⇑W) x|) := by rw [Real.norm_eq_abs]; ring
      _ ≤ a ^ n * C := mul_le_mul_of_nonneg_left (hC x) (by positivity)

lemma mehlerS'_apply {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 1) (W : 𝓢(ℝ, ℝ)) :
    ⇑(mehlerS' ha c hc W) = Mh a c W := rfl

/-- **`ℬ` is stable under the Mehler transform.** -/
lemma Bm.Mh {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 1) {f : ℝ → ℝ} (hf : Bm f) :
    Bm (Mh a c f) := by
  obtain ⟨W, hW⟩ := hf.deriv_schwartz
  obtain ⟨C, hC⟩ := hf.bdd
  refine ⟨sm_Mh' a c hf.sb, ⟨C, abs_Mh_le hf.sb a c hC⟩, a • mehlerS' ha c hc W, ?_⟩
  rw [deriv_Mh' hf.sb, ← hW]
  funext x
  simp [mehlerS'_apply]

end MarkovTriple.BGL.Instances.OUCompact
