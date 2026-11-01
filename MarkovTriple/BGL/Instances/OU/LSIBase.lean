import Mathlib
import MarkovTriple.BGL.Instances.OU.Full

/-!
# OU log-Sobolev / gradient bound (Part 1): analytic toolkit

* `ibpγ`: Gaussian integration by parts `∫ (G' − x G) dγ = 0` for `G` with bounded `G`, `G'`;
* `hasDerivAt_integral_γ`: differentiation under `∫ · dγ` with a linear-growth dominating function;
* `Bd`, `Lin`: uniform bounded / linear-growth families of functions of `(s, x)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

namespace MarkovTriple.BGL.Instances.OU

lemma φ_tendsto_atTop : Tendsto φ atTop (𝓝 0) := by
  have e : φ = fun x => (√(2 * π))⁻¹ * Real.exp (-(|x| ^ 2) / 2) := by
    funext x; rw [φ_def, sq_abs]
  rw [e]
  have h1 : Tendsto (fun x : ℝ => -(|x| ^ 2) / 2) atTop atBot := by
    have : Tendsto (fun x : ℝ => |x| ^ 2) atTop atTop :=
      (tendsto_pow_atTop (two_ne_zero)).comp tendsto_abs_atTop_atTop
    exact (tendsto_neg_atTop_atBot.comp this).atBot_div_const (by norm_num)
  simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (√(2 * π))⁻¹

lemma φ_tendsto_atBot : Tendsto φ atBot (𝓝 0) := by
  have e : φ = fun x => (√(2 * π))⁻¹ * Real.exp (-(|x| ^ 2) / 2) := by
    funext x; rw [φ_def, sq_abs]
  rw [e]
  have h1 : Tendsto (fun x : ℝ => -(|x| ^ 2) / 2) atBot atBot := by
    have : Tendsto (fun x : ℝ => |x| ^ 2) atBot atTop :=
      (tendsto_pow_atTop (two_ne_zero)).comp tendsto_abs_atBot_atTop
    exact (tendsto_neg_atTop_atBot.comp this).atBot_div_const (by norm_num)
  simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (√(2 * π))⁻¹

lemma integrable_lin {F : ℝ → ℝ} (hF : AEStronglyMeasurable F γ) {C : ℝ}
    (hb : ∀ x, |F x| ≤ C * (1 + |x|)) : Integrable F γ := by
  refine Integrable.mono' ((integrable_one_add_abs_pow 1).const_mul C) hF ?_
  exact ae_of_all _ fun x => by simpa using hb x

/-- **Gaussian integration by parts**: `∫ (G' − x G) dγ = 0` for `G` differentiable with `G, G'`
bounded. -/
theorem ibpγ {G G' : ℝ → ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (bG : ∃ C, ∀ x, |G x| ≤ C)
    (bG' : ∃ C, ∀ x, |G' x| ≤ C) :
    Integrable (fun x => G' x - x * G x) γ ∧ ∫ x, (G' x - x * G x) ∂γ = 0 := by
  obtain ⟨C, hC⟩ := bG
  obtain ⟨C', hC'⟩ := bG'
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hC0' : 0 ≤ C' := (abs_nonneg _).trans (hC' 0)
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hG'm : Measurable G' := by
    have : G' = deriv G := funext fun x => (hG x).deriv.symm
    rw [this]; exact measurable_deriv G
  have hint : Integrable (fun x => G' x - x * G x) γ := by
    refine integrable_lin ((hG'm.sub (measurable_id.mul hGc.measurable)).aestronglyMeasurable)
      (C := C' + C) fun x => ?_
    calc |G' x - x * G x| ≤ |G' x| + |x| * |G x| := by
          refine (abs_sub _ _).trans ?_; rw [abs_mul]
      _ ≤ C' + |x| * C := by
          gcongr
          · exact hC' x
          · exact hC x
      _ ≤ (C' + C) * (1 + |x|) := by nlinarith [abs_nonneg x]
  refine ⟨hint, ?_⟩
  rw [integral_γ]
  have hd : ∀ x, HasDerivAt (fun x => φ x * G x) (φ x * (G' x - x * G x)) x := by
    intro x
    have := (φ_hasDerivAt x).mul (hG x)
    convert this using 1; ring
  have hlim : ∀ l : Filter ℝ, Tendsto φ l (𝓝 0) → Tendsto (fun x => φ x * G x) l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (a := fun x => C * φ x) (fun x => ?_) (by simpa using hl.const_mul C)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (φ_pos x)]
    calc φ x * |G x| ≤ φ x * C := mul_le_mul_of_nonneg_left (hC x) (φ_pos x).le
      _ = C * φ x := by ring
  have := integral_of_hasDerivAt_of_tendsto hd (integrable_γ_iff.1 hint)
    (hlim _ φ_tendsto_atBot) (hlim _ φ_tendsto_atTop)
  simpa using this

/-- Differentiation under `∫ · dγ` with a dominating function of linear growth. -/
theorem hasDerivAt_integral_γ {H H' : ℝ → ℝ → ℝ} {s0 : ℝ} {S : Set ℝ} (hS : S ∈ 𝓝 s0)
    (hc : ∀ s ∈ S, Continuous (H s))
    (hH0 : ∃ C, ∀ x, |H s0 x| ≤ C * (1 + |x|))
    (hc' : Continuous (H' s0))
    (hd : ∀ x, ∀ s ∈ S, HasDerivAt (fun s => H s x) (H' s x) s)
    (hb : ∃ C, ∀ s ∈ S, ∀ x, |H' s x| ≤ C * (1 + |x|)) :
    Integrable (H' s0) γ ∧ HasDerivAt (fun s => ∫ x, H s x ∂γ) (∫ x, H' s0 x ∂γ) s0 := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨C0, hC0⟩ := hH0
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ) (F := fun s x => H s x)
    (F' := H') (x₀ := s0) (s := S) (bound := fun x => C * (1 + |x|)) hS
    (Filter.eventually_of_mem hS fun s hs => (hc s hs).aestronglyMeasurable)
    (integrable_lin (hc s0 (mem_of_mem_nhds hS)).aestronglyMeasurable hC0)
    hc'.aestronglyMeasurable
    (ae_of_all _ fun x s hs => by simpa using hC s hs x)
    ((integrable_one_add_abs_pow 1).const_mul C |>.congr (ae_of_all _ fun x => by simp))
    (ae_of_all _ fun x s hs => hd x s hs)
  exact h

/-! ### Uniformly bounded / linearly bounded families -/

/-- uniformly bounded family on `S` -/
def Bd (S : Set ℝ) (w : ℝ → ℝ → ℝ) : Prop := ∃ C, ∀ s ∈ S, ∀ x, |w s x| ≤ C

/-- uniformly linearly bounded family on `S` -/
def Lin (S : Set ℝ) (w : ℝ → ℝ → ℝ) : Prop := ∃ C, ∀ s ∈ S, ∀ x, |w s x| ≤ C * (1 + |x|)

variable {S : Set ℝ} {w v : ℝ → ℝ → ℝ}

lemma Bd.add (hw : Bd S w) (hv : Bd S v) : Bd S (fun s x => w s x + v s x) := by
  obtain ⟨C, hC⟩ := hw; obtain ⟨D, hD⟩ := hv
  exact ⟨C + D, fun s hs x => (abs_add_le _ _).trans (add_le_add (hC s hs x) (hD s hs x))⟩

lemma Bd.neg (hw : Bd S w) : Bd S (fun s x => -w s x) := by
  obtain ⟨C, hC⟩ := hw
  exact ⟨C, fun s hs x => by simpa using hC s hs x⟩

lemma Bd.sub (hw : Bd S w) (hv : Bd S v) : Bd S (fun s x => w s x - v s x) := by
  simpa [sub_eq_add_neg] using hw.add hv.neg

lemma Bd.mul (hw : Bd S w) (hv : Bd S v) : Bd S (fun s x => w s x * v s x) := by
  obtain ⟨C, hC⟩ := hw; obtain ⟨D, hD⟩ := hv
  refine ⟨C * D, fun s hs x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC s hs x) (hD s hs x) (abs_nonneg _) ((abs_nonneg _).trans (hC s hs x))

lemma bd_const (c : ℝ) : Bd S (fun _ _ => c) := ⟨|c|, fun _ _ _ => le_rfl⟩

lemma Lin.of_bd (hw : Bd S w) : Lin S w := by
  obtain ⟨C, hC⟩ := hw
  have hC0 : ∀ s ∈ S, ∀ x, 0 ≤ C := fun s hs x => (abs_nonneg _).trans (hC s hs x)
  refine ⟨|C|, fun s hs x => ?_⟩
  calc |w s x| ≤ C := hC s hs x
    _ ≤ |C| * 1 := by simpa using le_abs_self C
    _ ≤ |C| * (1 + |x|) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith [abs_nonneg x]

lemma Lin.add (hw : Lin S w) (hv : Lin S v) : Lin S (fun s x => w s x + v s x) := by
  obtain ⟨C, hC⟩ := hw; obtain ⟨D, hD⟩ := hv
  refine ⟨C + D, fun s hs x => ?_⟩
  calc |w s x + v s x| ≤ |w s x| + |v s x| := abs_add_le _ _
    _ ≤ C * (1 + |x|) + D * (1 + |x|) := add_le_add (hC s hs x) (hD s hs x)
    _ = _ := by ring

lemma Lin.neg (hw : Lin S w) : Lin S (fun s x => -w s x) := by
  obtain ⟨C, hC⟩ := hw
  exact ⟨C, fun s hs x => by simpa using hC s hs x⟩

lemma Lin.sub (hw : Lin S w) (hv : Lin S v) : Lin S (fun s x => w s x - v s x) := by
  simpa [sub_eq_add_neg] using hw.add hv.neg

lemma Lin.mul_bd (hw : Lin S w) (hv : Bd S v) : Lin S (fun s x => w s x * v s x) := by
  obtain ⟨C, hC⟩ := hw; obtain ⟨D, hD⟩ := hv
  refine ⟨C * D, fun s hs x => ?_⟩
  rw [abs_mul]
  calc |w s x| * |v s x| ≤ (C * (1 + |x|)) * D :=
        mul_le_mul (hC s hs x) (hD s hs x) (abs_nonneg _)
          ((abs_nonneg _).trans (hC s hs x))
    _ = _ := by ring

lemma Lin.bd_mul (hw : Bd S w) (hv : Lin S v) : Lin S (fun s x => w s x * v s x) := by
  simpa [mul_comm] using hv.mul_bd hw

lemma Bd.xmul (hw : Bd S w) : Lin S (fun s x => x * w s x) := by
  obtain ⟨C, hC⟩ := hw
  refine ⟨C, fun s hs x => ?_⟩
  rw [abs_mul]
  have h0 : 0 ≤ C := (abs_nonneg _).trans (hC s hs x)
  calc |x| * |w s x| ≤ |x| * C := mul_le_mul_of_nonneg_left (hC s hs x) (abs_nonneg _)
    _ ≤ C * (1 + |x|) := by nlinarith [abs_nonneg x]

end MarkovTriple.BGL.Instances.OU
