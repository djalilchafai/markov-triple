import Mathlib
import MarkovTriple.BGL.Instances.Circle.Modes
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Mass

/-!
# The Friedrichs semigroup of the circle acts diagonally on Fourier modes; smoothing (not frozen)

* generic (any `DiffusionTriple`): if `L f = -c f` pointwise (`f ∈ 𝒜₀`, `c ≥ 0`), the class of `f` is
  an eigenvector of the resolvent `R`, and `P_t [f] = e^{-ct} [f]` (`semigroup_cls_eigen`).  This is
  how the NEW (Friedrichs) `DiffusionTriple.semigroup` is connected to the Fourier action.
* circle: `P_t [mc n] = e^{-(2πn)² t} [mc n]`, same for `ms n`; by self-adjointness of `P_t`, the
  Fourier coefficients of `P_t u` are those of `u` times `e^{-(2πn)² t}`; hence, for `t > 0` and every
  `u ∈ L²`, `P_t u` is a.e. equal to a `C^∞` function (`smoothing`).
-/

namespace MarkovTriple.BGL

open MeasureTheory
open scoped NNReal

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

/-- Eigenvectors of `L` in `𝒜₀` are eigenvectors of the resolvent `R`. -/
lemma R_cls_eigen (f : T.A₀) {c : ℝ} (hc : 0 ≤ c) (h : T.Lcls f = (-c) • T.cls f) :
    (formData T).R (T.cls f) = (1 + c)⁻¹ • T.cls f := by
  have h1 := R_cls_sub T f
  have h2 : T.cls f - T.Lcls f = (1 + c) • T.cls f := by
    rw [h, add_smul, one_smul, neg_smul, sub_neg_eq_add]
  rw [h2, map_smul] at h1
  have hne : (1 + c) ≠ 0 := by positivity
  calc (formData T).R (T.cls f) = (1 + c)⁻¹ • ((1 + c) • (formData T).R (T.cls f)) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = _ := by rw [h1]

lemma Lcls_eq_smul {f : T.A₀} {c : ℝ} (h : ∀ x, T.L f.1 x = -c * f.1 x) :
    T.Lcls f = (-c) • T.cls f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_Lcls T f, coeFn_cls T f, Lp.coeFn_smul (-c) (T.cls f)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, h x, smul_eq_mul]

/-- **Eigenvectors of `L` are eigenvectors of the Friedrichs semigroup**: if `L f = -c f` pointwise
(`f ∈ 𝒜₀`, `c ≥ 0`), then `P_t [f] = e^{-ct} [f]`. -/
theorem semigroup_cls_eigen (f : T.A₀) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, T.L f.1 x = -c * f.1 x)
    (t : ℝ≥0) : T.semigroup t (T.cls f) = Real.exp (-c * t) • T.cls f :=
  (formData T).semigroup_eigen hc (R_cls_eigen T f hc (Lcls_eq_smul T h)) t

end DiffusionTriple

end MarkovTriple.BGL

namespace MarkovTriple.BGL.Circle
open MeasureTheory AddCircle Filter Topology
open scoped ENNReal NNReal Real InnerProductSpace
open MarkovTriple.Sanity.Circle
local notation "𝒜c" => MarkovTriple.Sanity.Circle.A₀

/-- the circle as a diffusion triple (`BGL/Sanity/Circle.lean`). -/
noncomputable abbrev cT : DiffusionTriple 𝕋 := MarkovTriple.BGL.Sanity.circleDiffusion

lemma cT_μ : cT.μ = μ₀ := rfl

/-- The Friedrichs semigroup of the circle triple, with `μ₀` visible in its type. -/
noncomputable def semigroupC (t : ℝ≥0) : Lp ℝ 2 μ₀ →L[ℝ] Lp ℝ 2 μ₀ := cT.semigroup t

noncomputable def mcL (n : ℤ) : Lp ℝ 2 μ₀ := (memLp_of_mem (mc_mem n) 2).toLp (mc n)
noncomputable def msL (n : ℤ) : Lp ℝ 2 μ₀ := (memLp_of_mem (ms_mem n) 2).toLp (ms n)

lemma cls_mc (n : ℤ) : cT.cls ⟨mc n, mc_mem n⟩ = mcL n := rfl
lemma cls_ms (n : ℤ) : cT.cls ⟨ms n, ms_mem n⟩ = msL n := rfl

lemma semigroup_mc (t : ℝ≥0) (n : ℤ) :
    semigroupC t (mcL n) = Real.exp (-lam n * t) • mcL n :=
  DiffusionTriple.semigroup_cls_eigen cT ⟨mc n, mc_mem n⟩ (lam_nonneg n)
    (fun x => by
      have := congrFun (Lc_mc n) x
      show Lc (mc n) x = _
      simpa using this) t

lemma semigroup_ms (t : ℝ≥0) (n : ℤ) :
    semigroupC t (msL n) = Real.exp (-lam n * t) • msL n :=
  DiffusionTriple.semigroup_cls_eigen cT ⟨ms n, ms_mem n⟩ (lam_nonneg n)
    (fun x => by
      have := congrFun (Lc_ms n) x
      show Lc (ms n) x = _
      simpa using this) t

/-- complexification of an `L²` class -/
noncomputable def liftC (v : Lp ℝ 2 μ₀) : Lp ℂ 2 μ₀ := Complex.ofRealCLM.compLp v

lemma coeFn_liftC (v : Lp ℝ 2 μ₀) :
    (liftC v : 𝕋 → ℂ) =ᵐ[μ₀] fun x => ((v x : ℝ) : ℂ) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp Complex.ofRealCLM v] with x hx
  simpa [liftC] using hx

lemma inner_toLp_left {a : 𝕋 → ℝ} (ha : a ∈ 𝒜c) (v : Lp ℝ 2 μ₀) :
    inner ℝ ((memLp_of_mem ha 2).toLp a) (v) = ∫ x, a x * v x ∂μ₀ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_of_mem ha 2).coeFn_toLp] with x h1
  rw [h1]
  simp [mul_comm]

lemma integrable_mul_Lp {a : 𝕋 → ℝ} (ha : a ∈ 𝒜c) (v : Lp ℝ 2 μ₀) :
    Integrable (fun x => a x * v x) μ₀ := by
  have := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) ((memLp_of_mem ha 2).toLp a) v
  refine (this.congr ?_)
  filter_upwards [(memLp_of_mem ha 2).coeFn_toLp] with x h1
  rw [h1]; simp [mul_comm]

lemma repr_liftC (v : Lp ℝ 2 μ₀) (n : ℤ) :
    (fourierBasis (T := 1)).repr (liftC v) n =
      ((inner ℝ (mcL n) (v) : ℝ) : ℂ) - Complex.I * ((inner ℝ (msL n) (v) : ℝ) : ℂ) := by
  rw [fourierBasis_repr, fourierCoeff]
  have h1 : inner ℝ (mcL n) (v) = ∫ x, mc n x * v x ∂μ₀ := inner_toLp_left (mc_mem n) v
  have h2 : inner ℝ (msL n) (v) = ∫ x, ms n x * v x ∂μ₀ := inner_toLp_left (ms_mem n) v
  rw [h1, h2]
  have e : ∀ x : 𝕋, fourier (-n) x * ((v x : ℝ) : ℂ) =
      ((mc n x * v x : ℝ) : ℂ) - Complex.I * ((ms n x * v x : ℝ) : ℂ) := by
    intro x
    rw [fourier_neg]
    apply Complex.ext <;> simp [mc, ms]
  have i1 := (integrable_mul_Lp (mc_mem n) v).ofReal (𝕜 := ℂ)
  have i2 := ((integrable_mul_Lp (ms_mem n) v).ofReal (𝕜 := ℂ)).const_mul Complex.I
  calc ∫ t, fourier (-n) t • (liftC v) t ∂μ₀
      = ∫ t, (((mc n t * v t : ℝ) : ℂ) - Complex.I * ((ms n t * v t : ℝ) : ℂ)) ∂μ₀ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_liftC v] with x hx
        rw [smul_eq_mul, hx, e]
    _ = _ := by
        refine (integral_sub i1 i2).trans ?_
        rw [integral_const_mul, integral_ofReal, integral_ofReal]
        rfl

lemma norm_repr_le (w : Lp ℂ 2 μ₀) (n : ℤ) : ‖(fourierBasis (T := 1)).repr w n‖ ≤ ‖w‖ := by
  rw [HilbertBasis.repr_apply_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  have : ‖(fourierBasis (T := 1)) n‖ = 1 := (fourierBasis (T := 1)).orthonormal.1 n
  rw [this, one_mul]

lemma inner_semigroup (t : ℝ≥0) (u v : Lp ℝ 2 μ₀) :
    inner ℝ (semigroupC t u) v = inner ℝ u (semigroupC t v) := by
  have h : IsSelfAdjoint (semigroupC t) := DiffusionTriple.semigroup_isSelfAdjoint cT t
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h) u v

lemma repr_P (t : ℝ≥0) (u : Lp ℝ 2 μ₀) (n : ℤ) :
    (fourierBasis (T := 1)).repr (liftC (semigroupC t u)) n =
      ((Real.exp (-lam n * t) : ℝ) : ℂ) * (fourierBasis (T := 1)).repr (liftC u) n := by
  refine (repr_liftC (semigroupC t u) n).trans ?_
  rw [repr_liftC u n]
  have h1 : inner ℝ (mcL n) (semigroupC t u) = Real.exp (-lam n * t) * inner ℝ (mcL n) (u) := by
    rw [← inner_semigroup, semigroup_mc, inner_smul_left]; simp
  have h2 : inner ℝ (msL n) (semigroupC t u) = Real.exp (-lam n * t) * inner ℝ (msL n) (u) := by
    rw [← inner_semigroup, semigroup_ms, inner_smul_left]; simp
  rw [h1, h2]; push_cast; ring

/-- **Smoothing**: for `t > 0`, `P_t u` is (a.e. equal to) a `C^∞` function, for every `u ∈ L²`. -/
theorem smoothing {t : ℝ≥0} (ht : 0 < t) (u : Lp ℝ 2 μ₀) :
    ∃ g ∈ 𝒜c, ((semigroupC t u : Lp ℝ 2 μ₀) : 𝕋 → ℝ) =ᵐ[μ₀] g := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  set w : Lp ℂ 2 μ₀ := liftC (semigroupC t u) with hw
  set b : ℤ → ℂ := fun n => (fourierBasis (T := 1)).repr w n with hb
  have hb' : ∀ n, b n = ((Real.exp (-lam n * t) : ℝ) : ℂ) * (fourierBasis (T := 1)).repr (liftC u) n :=
    fun n => repr_P t u n
  set a : ℝ := (2 * π) ^ 2 * t with ha
  have hapos : 0 < a := by positivity
  have hbound : ∀ n, ‖b n‖ ≤ ‖liftC u‖ * Real.exp (-(a * (n : ℝ) ^ 2)) := by
    intro n
    rw [hb', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have e : -lam n * t = -(a * (n : ℝ) ^ 2) := by simp only [lam, ha]; ring
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_repr_le _ n) (Real.exp_pos _).le
  have hrap : Rapid b := Rapid.of_gauss hapos hbound
  -- the continuous function `G`
  have hnorm : Summable fun n : ℤ => ‖b n • (fourier n : C(𝕋, ℂ))‖ := by
    refine hrap.summable.congr fun n => ?_
    rw [norm_smul, fourier_norm, mul_one]
  have hsm : Summable (fun n : ℤ => b n • (fourier n : C(𝕋, ℂ))) := Summable.of_norm hnorm
  have hsum : HasSum (fun n : ℤ => b n • (fourier n : C(𝕋, ℂ))) (∑' n : ℤ, b n • (fourier n : C(𝕋, ℂ))) :=
    hsm.hasSum
  obtain ⟨G, hG⟩ : ∃ G : C(𝕋, ℂ), G = ∑' n : ℤ, b n • (fourier n : C(𝕋, ℂ)) := ⟨_, rfl⟩
  rw [← hG] at hsum
  have hL := (ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ).hasSum hsum
  have hL2 : HasSum (fun n : ℤ => b n • (fourierLp (T := 1) 2 n)) w := by
    have := hasSum_fourier_series_L2 w
    simpa only [← fourierBasis_repr] using this
  have hLw : HasSum (fun n : ℤ => b n • (fourierLp (T := 1) 2 n))
      (ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ G) := by
    have e : ∀ n : ℤ, ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ (b n • (fourier n : C(𝕋, ℂ))) =
        b n • (fourierLp (T := 1) 2 n) := fun n => map_smul _ _ _
    have e' : (fun n : ℤ => ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ (b n • (fourier n : C(𝕋, ℂ)))) =
        fun n : ℤ => b n • (fourierLp (T := 1) 2 n) := funext e
    rw [← e']; exact hL
  have hwG : w = ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ G := hL2.unique hLw
  have hae : (w : 𝕋 → ℂ) =ᵐ[μ₀] G := by
    rw [hwG]; exact ContinuousMap.coeFn_toLp _ _
  have hGs : (fun s : ℝ => G (s : 𝕋)) = ser b := by
    funext s
    have h := ContinuousMap.tsum_apply hsm (s : 𝕋)
    rw [hG]
    refine h.symm.trans ?_
    simp [ser]
  refine ⟨fun x => (G x).re, ?_, ?_⟩
  · rw [mem_A₀]
    have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => G (s : 𝕋)) := by
      rw [hGs]; exact contDiff_ser hrap
    exact Complex.reCLM.contDiff.comp h3
  · filter_upwards [hae, coeFn_liftC (semigroupC t u)] with x h1 h2
    rw [hw] at h1
    have : ((semigroupC t u : Lp ℝ 2 μ₀) x : ℂ) = G x := by rw [← h2, ← h1]
    rw [← this]; simp

end MarkovTriple.BGL.Circle
