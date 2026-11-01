import Mathlib
import MarkovTriple.BGL.Instances.Circle.Semigroup
import MarkovTriple.BGL.Semigroup.Mass

/-!
# Ergodicity (S10) and conservativeness (S11) of the circle (not frozen)

* S10: if `u ∈ 𝒟(L)` and `L u = 0`, then `R u = u` for the resolvent `R = (1-L)⁻¹`; testing against the
  real Fourier modes (eigenvectors of `R` with eigenvalue `(1+(2πn)²)⁻¹ ≠ 1` for `n ≠ 0`) shows that all
  non-zero Fourier coefficients of `u` vanish, so `u` is a.e. constant.
* S11: `P_t [1] = [1]` (the mode `n = 0`), then `conservative_of_semigroup_one`.
-/

namespace MarkovTriple.BGL.Circle
open MeasureTheory AddCircle Filter Topology
open scoped ENNReal NNReal Real InnerProductSpace
open MarkovTriple.Sanity.Circle
local notation "𝒜c" => MarkovTriple.Sanity.Circle.A₀

instance : IsFiniteMeasure cT.μ := inferInstanceAs (IsFiniteMeasure μ₀)

/-- the resolvent `R = (1 - L)⁻¹` of the circle triple, with `μ₀` visible in its type. -/
noncomputable def RC : Lp ℝ 2 μ₀ →L[ℝ] Lp ℝ 2 μ₀ := (DiffusionTriple.formData cT).R

lemma RC_mc (n : ℤ) : RC (mcL n) = (1 + lam n)⁻¹ • mcL n :=
  DiffusionTriple.R_cls_eigen cT ⟨mc n, mc_mem n⟩ (lam_nonneg n)
    (DiffusionTriple.Lcls_eq_smul cT (fun x => by
      have := congrFun (Lc_mc n) x
      show Lc (mc n) x = _
      simpa using this))

lemma RC_ms (n : ℤ) : RC (msL n) = (1 + lam n)⁻¹ • msL n :=
  DiffusionTriple.R_cls_eigen cT ⟨ms n, ms_mem n⟩ (lam_nonneg n)
    (DiffusionTriple.Lcls_eq_smul cT (fun x => by
      have := congrFun (Lc_ms n) x
      show Lc (ms n) x = _
      simpa using this))

lemma inner_RC (u v : Lp ℝ 2 μ₀) : inner ℝ (RC u) v = inner ℝ u (RC v) := by
  have h : IsSelfAdjoint RC := (DiffusionTriple.formData cT).R_isSelfAdjoint
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h) u v

lemma inner_eq_zero_of_fixed {u a : Lp ℝ 2 μ₀} {c : ℝ} (hc : 0 < c) (hu : RC u = u)
    (ha : RC a = (1 + c)⁻¹ • a) : inner ℝ a u = 0 := by
  have h1 : inner ℝ u a = inner ℝ u a * (1 + c)⁻¹ := by
    calc inner ℝ u a = inner ℝ (RC u) a := by rw [hu]
      _ = inner ℝ u (RC a) := inner_RC u a
      _ = _ := by rw [ha, inner_smul_right, mul_comm]
  have h2 : inner ℝ u a = 0 := by
    have hk : (1 + c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    by_contra hne
    have : (1 : ℝ) = (1 + c)⁻¹ := by
      have := mul_left_cancel₀ hne (show inner ℝ u a * 1 = inner ℝ u a * (1 + c)⁻¹ by
        rw [mul_one]; exact h1)
      exact this
    linarith
  rw [real_inner_comm]; exact h2

lemma lam_pos {n : ℤ} (hn : n ≠ 0) : 0 < lam n := by
  unfold lam
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  positivity

/-- A function in `L²(𝕋)` all of whose non-zero Fourier coefficients vanish is a.e. constant. -/
lemma ae_const_of_repr_zero (u : Lp ℝ 2 μ₀)
    (h : ∀ n : ℤ, n ≠ 0 → (fourierBasis (T := 1)).repr (liftC u) n = 0) :
    ∃ c : ℝ, (u : 𝕋 → ℝ) =ᵐ[μ₀] fun _ => c := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hs := hasSum_fourier_series_L2 (liftC u)
  simp only [← fourierBasis_repr] at hs
  have h1 : HasSum (fun n : ℤ => (fourierBasis (T := 1)).repr (liftC u) n • (fourierLp (T := 1) 2 n))
      ((fourierBasis (T := 1)).repr (liftC u) 0 • (fourierLp (T := 1) 2 0)) :=
    hasSum_single 0 (fun n hn => by rw [h n hn, zero_smul])
  have h2 := hs.unique h1
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (fourierBasis (T := 1)).repr (liftC u) 0 := ⟨_, rfl⟩
  rw [← hc] at h2
  refine ⟨c.re, ?_⟩
  filter_upwards [coeFn_liftC u, Lp.coeFn_smul c
    (fourierLp (T := 1) 2 0), coeFn_fourierLp (T := 1) 2 0] with x hx hy hz
  have e1 : ((u x : ℝ) : ℂ) = c := by
    rw [← hx, h2, hy]
    simp only [Pi.smul_apply, smul_eq_mul, hz, fourier_zero, mul_one]
  have := congrArg Complex.re e1
  simpa using this

/-- **S10 for the circle**: `u ∈ 𝒟(L)`, `L u = 0` ⇒ `u` is a.e. constant. -/
theorem circle_ergodic (u : Lp ℝ 2 cT.μ) (hu : u ∈ cT.generator.domain)
    (hG : cT.generator ⟨u, hu⟩ = 0) : ∃ c : ℝ, (u : 𝕋 → ℝ) =ᵐ[cT.μ] fun _ => c := by
  have hR : (DiffusionTriple.formData cT).R (u - 0) = u :=
    ((DiffusionTriple.formData cT).generator_apply_eq_iff hu 0).1 hG
  rw [sub_zero] at hR
  have hR' : RC (u : Lp ℝ 2 μ₀) = u := hR
  refine ae_const_of_repr_zero (u : Lp ℝ 2 μ₀) (fun n hn => ?_)
  refine (repr_liftC (u : Lp ℝ 2 μ₀) n).trans ?_
  rw [inner_eq_zero_of_fixed (lam_pos hn) hR' (RC_mc n),
    inner_eq_zero_of_fixed (lam_pos hn) hR' (RC_ms n)]
  simp

/-- the constant `1` as a class in `L²(μ₀)`. -/
noncomputable def one2C : Lp ℝ 2 μ₀ := (memLp_const (1 : ℝ)).toLp _

lemma mcL_zero_eq_one2 : (mcL 0 : Lp ℝ 2 μ₀) = one2C := by
  refine Lp.ext ?_
  filter_upwards [(memLp_of_mem (mc_mem 0) 2).coeFn_toLp,
    MemLp.coeFn_toLp (memLp_const (1 : ℝ)) (μ := μ₀)] with x h1 h2
  rw [show (mcL 0 : 𝕋 → ℝ) x = mc 0 x from h1, show (one2C : 𝕋 → ℝ) x = 1 from h2]
  simp [mc]

lemma semigroup_one (t : ℝ≥0) : cT.semigroup t cT.one2 = cT.one2 := by
  have h := semigroup_mc t 0
  rw [mcL_zero_eq_one2] at h
  have e : Real.exp (-lam 0 * t) = 1 := by simp [lam]
  rw [e, one_smul] at h
  exact h

end MarkovTriple.BGL.Circle
