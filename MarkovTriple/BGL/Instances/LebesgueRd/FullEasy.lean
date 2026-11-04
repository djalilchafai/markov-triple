import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Gamma2
import MarkovTriple.BGL.Frozen.FullTriple

/-!
# The elementary fields F1–F7, F9 of the Brownian full triple on `(ℝ^d, Lebesgue)` (stage S3a)

`F8` (semigroup regularity), `F10` (ESA), `S10`, `S11` are NOT here.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

/-! ### Second-order chain rule -/

lemma contDiff_pderiv {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin k) :
    ContDiff ℝ (⊤ : ℕ∞) (MarkovTriple.BGL.pderiv ψ i) :=
  MarkovTriple.BGL.Lebesgue.contDiff_pderiv ψ hψ i

/-- Second-order chain rule: `Δ(ψ∘f) = Σ ∂ⱼψ Δfⱼ + Σ ∂ₗ∂ⱼψ Γ(fⱼ,fₗ)`. -/
lemma Lf_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin d → ℝ) → ℝ) (hf : ∀ i, Sm (f i)) :
    Lf (fun x => ψ (fun i => f i x)) =
      fun x => ∑ j, MarkovTriple.BGL.pderiv ψ j (fun l => f l x) * Lf (f j) x +
        ∑ j, ∑ l, MarkovTriple.BGL.pderiv₂ ψ j l (fun m => f m x) * Gf (f j) (f l) x := by
  funext x
  have h1 : ∀ i, dd i (fun y => ψ (fun j => f j y)) =
      fun y => ∑ j, MarkovTriple.BGL.pderiv ψ j (fun l => f l y) * dd i (f j) y :=
    fun i => funext (dd_comp ψ hψ f hf i)
  have hP : ∀ j, Sm (fun y => MarkovTriple.BGL.pderiv ψ j (fun l => f l y)) :=
    fun j => comp_sm _ (contDiff_pderiv ψ hψ j) f hf
  have hterm : ∀ i j, Sm (fun y => MarkovTriple.BGL.pderiv ψ j (fun l => f l y) * dd i (f j) y) :=
    fun i j => (hP j).mul ((hf j).dd i)
  have h2 : ∀ i, dd i (dd i (fun y => ψ (fun j => f j y))) x =
      ∑ j, ((∑ l, MarkovTriple.BGL.pderiv₂ ψ j l (fun m => f m x) * dd i (f l) x) * dd i (f j) x +
        MarkovTriple.BGL.pderiv ψ j (fun l => f l x) * dd i (dd i (f j)) x) := by
    intro i
    rw [h1 i, dd_fsum (hterm i) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (fun y => MarkovTriple.BGL.pderiv ψ j (fun l => f l y) * dd i (f j) y) =
      (fun y => MarkovTriple.BGL.pderiv ψ j (fun l => f l y)) * dd i (f j) from rfl,
      dd_mul (hP j) ((hf j).dd i) i x,
      dd_comp (MarkovTriple.BGL.pderiv ψ j) (contDiff_pderiv ψ hψ j) f hf i x]
    rfl
  unfold Lf Gf
  simp only [h2, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.mul_sum]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

/-! ### Fields -/

lemma F1 {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A d) {h : (Fin d → ℝ) → ℝ} (hh : h ∈ A₀ d) :
    h * f ∈ A₀ d :=
  mem_A₀.2 ⟨(smooth hh).mul hf, (cs hh).mul_right⟩

lemma A_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin d → ℝ) → ℝ) (hf : ∀ i, f i ∈ A d) :
    (fun x => ψ (fun i => f i x)) ∈ A d := comp_sm ψ hψ f hf

lemma L_mem_A {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A d) : Lf f ∈ A d := by
  have : Lf f = fun y => ∑ i, dd i (dd i f) y := rfl
  have hs : Sm f := mem_A.1 hf
  rw [mem_A, this]
  exact ContDiff.sum fun i _ => (hs.dd i).dd i

lemma F5 (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A d) :
    0 ≤ᵐ[volume] (lebesgueRdDiffusion d hd).ΓA f f := by
  rw [ΓA_eq_Gf hd (mem_A.1 hf) (mem_A.1 hf)]
  exact Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma F6Γ (hd : 1 ≤ d) (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin d → ℝ) → ℝ) (hf : ∀ i, f i ∈ A d) {g : (Fin d → ℝ) → ℝ} (hg : g ∈ A d) :
    (lebesgueRdDiffusion d hd).ΓA (fun x => ψ (fun i => f i x)) g =ᵐ[volume]
      fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) *
        (lebesgueRdDiffusion d hd).ΓA (f i) g x := by
  refine Filter.Eventually.of_forall fun x => ?_
  rw [ΓA_eq_Gf hd (comp_sm ψ hψ f hf) (mem_A.1 hg)]
  have := congrFun (Gf_comp ψ hψ f hf g) x
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by rw [ΓA_eq_Gf hd (hf i) (mem_A.1 hg)]

lemma F6L (hd : 1 ≤ d) (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin d → ℝ) → ℝ) (hf : ∀ i, f i ∈ A d) :
    Lf (fun x => ψ (fun i => f i x)) =ᵐ[volume]
      fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * Lf (f i) x +
        ∑ i, ∑ j, MarkovTriple.BGL.pderiv₂ ψ i j (fun l => f l x) *
          (lebesgueRdDiffusion d hd).ΓA (f i) (f j) x := by
  refine Filter.Eventually.of_forall fun x => ?_
  have := congrFun (Lf_comp ψ hψ f hf) x
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ΓA_eq_Gf hd (hf i) (hf j)]

lemma ibp_L' {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : g ∈ A₀ d) :
    ∫ x, f x * Lf g x = -∫ x, Gf f g x := by
  have hint : ∀ i, Integrable (fun x => f x * dd i (dd i g) x) := fun i =>
    (hf.continuous.mul (((smooth hg).dd i).dd i).continuous).integrable_of_hasCompactSupport
      (cs_dd (cs_dd (cs hg) i) i).mul_left
  have hint2 : ∀ i, Integrable (fun x => dd i f x * dd i g x) := fun i =>
    ((hf.dd i).continuous.mul ((smooth hg).dd i).continuous).integrable_of_hasCompactSupport
      (cs_dd (cs hg) i).mul_left
  have e1 : (fun x => f x * Lf g x) = fun x => ∑ i, f x * dd i (dd i g) x := by
    funext x; simp [Lf, Finset.mul_sum]
  have e2 : (fun x => Gf f g x) = fun x => ∑ i, dd i f x * dd i g x := rfl
  rw [e1, e2, integral_finsetSum _ (fun i _ => hint i), integral_finsetSum _ (fun i _ => hint2 i),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ibp_cs hf ((smooth hg).dd i) (Or.inr (cs_dd (cs hg) i)) i]

lemma F7 (hd : 1 ≤ d) {f g : (Fin d → ℝ) → ℝ} (hf : f ∈ A d) (hg : g ∈ A₀ d) :
    ∫ x, (lebesgueRdDiffusion d hd).ΓA f g x = -∫ x, g x * Lf f x ∧
      ∫ x, (lebesgueRdDiffusion d hd).ΓA f g x = -∫ x, f x * Lf g x := by
  rw [ΓA_eq_Gf hd (mem_A.1 hf) (smooth hg)]
  exact ⟨by rw [ibp_L (mem_A.1 hf) hg]; simp, by rw [ibp_L' (mem_A.1 hf) hg]; simp⟩

/-- a smooth compactly supported bump, positive exactly on `{|y - x₀|² < r²}`. -/
noncomputable def bump (x₀ : Fin d → ℝ) (r : ℝ) (y : Fin d → ℝ) : ℝ :=
  Real.smoothTransition (1 - sq (y - x₀) / r ^ 2)

lemma bump_smooth (x₀ : Fin d → ℝ) (r : ℝ) : Sm (bump x₀ r) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((sq_smooth.comp (contDiff_id.sub contDiff_const)).div_const _))

lemma bump_pos {x₀ y : Fin d → ℝ} {r : ℝ} (hr : 0 < r) (h : sq (y - x₀) < r ^ 2) :
    0 < bump x₀ r y := by
  unfold bump
  apply Real.smoothTransition.pos_of_pos
  have : sq (y - x₀) / r ^ 2 < 1 := (div_lt_one (by positivity)).2 h
  linarith

lemma bump_zero {x₀ y : Fin d → ℝ} {r : ℝ} (hr : 0 < r) (h : r ^ 2 ≤ sq (y - x₀)) :
    bump x₀ r y = 0 := by
  unfold bump
  apply Real.smoothTransition.zero_of_nonpos
  have : 1 ≤ sq (y - x₀) / r ^ 2 := (one_le_div (by positivity)).2 h
  linarith

lemma bump_cs (x₀ : Fin d → ℝ) {r : ℝ} (hr : 0 < r) : HasCompactSupport (bump x₀ r) := by
  refine HasCompactSupport.intro (K := Metric.closedBall x₀ r) (isCompact_closedBall _ _)
    fun y hy => bump_zero hr ?_
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have : ∃ i, r < |(y - x₀) i| := by
    by_contra h
    push Not at h
    exact hy ((pi_norm_le_iff_of_nonneg hr.le).2 fun i => by simpa using h i)
  obtain ⟨i, hi⟩ := this
  have h1 : (y - x₀) i ^ 2 ≤ sq (y - x₀) :=
    Finset.single_le_sum (f := fun i => (y - x₀) i ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have h2 : r ^ 2 < (y - x₀) i ^ 2 := by
    rw [← sq_abs ((y - x₀) i)]; exact pow_lt_pow_left₀ hi hr.le (by norm_num)
  linarith

lemma bump_mem (x₀ : Fin d → ℝ) {r : ℝ} (hr : 0 < r) : bump x₀ r ∈ A₀ d :=
  mem_A₀.2 ⟨bump_smooth x₀ r, bump_cs x₀ hr⟩

lemma F2 {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A d)
    (h : ∀ h ∈ A₀ d, 0 ≤ᵐ[volume] h → 0 ≤ ∫ x, h x * f x) : 0 ≤ᵐ[volume] f := by
  have hfc : Continuous f := (mem_A.1 hf).continuous
  have hall : ∀ x, 0 ≤ f x := by
    intro x0
    by_contra hneg
    push Not at hneg
    have hopen : IsOpen {x | f x < 0} := isOpen_lt hfc continuous_const
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen x0 hneg
    have hb0 : ∀ x, 0 ≤ bump x0 r x := fun x => Real.smoothTransition.nonneg _
    have hneg' : ∀ x, bump x0 r x * f x ≤ 0 := by
      intro x
      by_cases hx : x ∈ Metric.ball x0 r
      · exact mul_nonpos_of_nonneg_of_nonpos (hb0 x) (hball hx).le
      · have : bump x0 r x = 0 := by
          apply bump_zero hr
          by_contra hlt
          push Not at hlt
          apply hx
          rw [Metric.mem_ball, dist_eq_norm]
          refine (pi_norm_lt_iff hr).2 fun i => ?_
          have h1 : (x - x0) i ^ 2 ≤ sq (x - x0) :=
            Finset.single_le_sum (f := fun i => (x - x0) i ^ 2) (fun j _ => by positivity)
              (Finset.mem_univ i)
          have : |(x - x0) i| < r := by
            apply abs_lt_of_sq_lt_sq (by nlinarith) hr.le
          simpa using this
        simp [this]
    have hpos : 0 < ∫ x, -(bump x0 r x * f x) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x0)
        (((bump_smooth x0 r).continuous.mul hfc).neg) ?_ (fun x => by simpa using hneg' x) ?_
      · exact ((bump_cs x0 hr).mul_right).neg
      · have h1 : 0 < bump x0 r x0 := bump_pos hr (by simp [sq]; positivity)
        have : bump x0 r x0 * f x0 < 0 := mul_neg_of_pos_of_neg h1 hneg
        simpa using this.ne
    have := h _ (bump_mem x0 hr) (Filter.Eventually.of_forall hb0)
    rw [integral_neg] at hpos
    linarith
  exact Filter.Eventually.of_forall hall

lemma F9 (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A d)
    (h0 : (lebesgueRdDiffusion d hd).ΓA f f =ᵐ[volume] 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  have hf' : Sm f := mem_A.1 hf
  rw [ΓA_eq_Gf hd hf' hf'] at h0
  have h1 : ∀ i, dd i f =ᵐ[volume] 0 := by
    intro i
    filter_upwards [h0] with x hx
    simp only [Gf, Pi.zero_apply] at hx
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (dd j f x))).1 hx i (Finset.mem_univ i)
    exact mul_self_eq_zero.1 hz
  have h2 : ∀ i x, dd i f x = 0 := fun i x =>
    congrFun ((Continuous.ae_eq_iff_eq volume (hf'.dd i).continuous continuous_const).1 (h1 i)) x
  have h3 : ∀ x, fderiv ℝ f x = 0 := by
    intro x
    ext v
    rw [MarkovTriple.BGL.Lebesgue.clm_pi_apply]
    simp only [zero_apply]
    exact Finset.sum_eq_zero fun i _ => by
      have := h2 i x; unfold dd at this; rw [this]; simp
  have := is_const_of_fderiv_eq_zero (hf'.differentiable (by simp)) h3
  exact ⟨f 0, Filter.Eventually.of_forall fun x => this x 0⟩

end MarkovTriple.BGL.LebesgueRd
