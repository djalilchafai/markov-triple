import Mathlib
import MarkovTriple.BGL.Sanity.Circle

/-!
# Fourier modes of the circle and rapidly decaying Fourier series (not frozen)

Ported (with adaptations) from the old `Sanity/CircleFull.lean`: the real Fourier modes
`mc n = cos 2πn·`, `ms n = sin 2πn·` are smooth eigenfunctions of `L f = f''` with eigenvalue
`-(2πn)²`; Fourier series with rapidly decaying coefficients are `C^∞` functions.
-/

namespace MarkovTriple.BGL.Circle
open MeasureTheory AddCircle Filter Topology
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.Circle
local notation "𝒜c" => MarkovTriple.Sanity.Circle.A₀

noncomputable def mc (n : ℤ) : 𝕋 → ℝ := fun x => (fourier n x).re
/-- imaginary part of `e^{2πinx}` -/
noncomputable def ms (n : ℤ) : 𝕋 → ℝ := fun x => (fourier n x).im

lemma fourier_pt_add (n : ℤ) (x y : 𝕋) : fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

lemma contDiff_fourier_coe (n : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => fourier n (t : 𝕋)) := by
  have : (fun t : ℝ => fourier n (t : 𝕋)) =
      fun t : ℝ => Complex.exp (2 * π * Complex.I * n / ((1:ℝ):ℂ) * t) := by
    funext t; rw [fourier_coe_apply]; congr 1; ring
  rw [this]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (2 * π * Complex.I * n / ((1:ℝ):ℂ)) * (t : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff (𝕜 := ℝ))
  have hexp : ContDiff ℝ (⊤ : ℕ∞) Complex.exp :=
    Complex.contDiff_exp (𝕜 := ℝ) (n := (⊤ : ℕ∞))
  exact hexp.comp h1

lemma mc_mem (n : ℤ) : mc n ∈ 𝒜c := by
  rw [mem_A₀]; exact Complex.reCLM.contDiff.comp (contDiff_fourier_coe n)

lemma ms_mem (n : ℤ) : ms n ∈ 𝒜c := by
  rw [mem_A₀]; exact Complex.imCLM.contDiff.comp (contDiff_fourier_coe n)

lemma hasDerivAt_fourier_shift (n : ℤ) (x : 𝕋) :
    HasDerivAt (fun t : ℝ => fourier n (x + (t : 𝕋)))
      (fourier n x * (2 * π * Complex.I * n)) 0 := by
  have h := hasDerivAt_fourier (1:ℝ) n 0
  simp only [fourier_pt_add]
  have h2 := h.const_mul (fourier n x)
  convert h2 using 1
  simp

lemma D_mc (n : ℤ) : D (mc n) = (-(2 * π * n)) • ms n := by
  funext x
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_fourier_shift n x))
  have : D (mc n) x = _ := h.deriv
  rw [this]
  simp [ms]; ring

lemma D_ms (n : ℤ) : D (ms n) = (2 * π * n) • mc n := by
  funext x
  have h := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_fourier_shift n x))
  have : D (ms n) x = _ := h.deriv
  rw [this]
  simp [mc]; ring

/-- eigenvalue of `-L` on mode `n` -/
noncomputable def lam (n : ℤ) : ℝ := (2 * π * n) ^ 2

lemma lam_nonneg (n : ℤ) : 0 ≤ lam n := sq_nonneg _

lemma Lc_mc (n : ℤ) : Lc (mc n) = (-lam n) • mc n := by
  unfold Lc
  rw [D_mc, D_smul _ (Sm_of_mem (ms_mem n)), D_ms]
  funext x; simp [lam]; ring

lemma Lc_ms (n : ℤ) : Lc (ms n) = (-lam n) • ms n := by
  unfold Lc
  rw [D_ms, D_smul _ (Sm_of_mem (mc_mem n)), D_mc]
  funext x; simp [lam]; ring

lemma norm_fourier_pt (n : ℤ) (x : 𝕋) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/-- Fourier series with coefficients `c`, as a function of `s ∈ ℝ`. -/
noncomputable def ser (c : ℤ → ℂ) (s : ℝ) : ℂ := ∑' n : ℤ, c n * fourier n (s : 𝕋)

/-- rapid decay -/
def Rapid (c : ℤ → ℂ) : Prop := ∀ k : ℕ, Summable fun n : ℤ => (|(n : ℝ)|) ^ k * ‖c n‖

noncomputable def dcf (c : ℤ → ℂ) : ℤ → ℂ := fun n => (2 * π * Complex.I * n) * c n

lemma Rapid.d {c : ℤ → ℂ} (hc : Rapid c) : Rapid (dcf c) := by
  intro k
  have h := (hc (k + 1)).mul_left (2 * π)
  refine h.congr fun n => ?_
  simp [dcf, abs_of_pos Real.pi_pos]
  ring

lemma Rapid.summable {c : ℤ → ℂ} (hc : Rapid c) : Summable fun n => ‖c n‖ := by
  simpa using hc 0

lemma hasDerivAt_ser {c : ℤ → ℂ} (hc : Rapid c) (s : ℝ) :
    HasDerivAt (ser c) (ser (dcf c) s) s := by
  have hu : Summable fun n : ℤ => ‖dcf c n‖ := by simpa using (hc.d).summable
  have := hasDerivAt_tsum (𝕜 := ℝ) (g := fun (n : ℤ) (y : ℝ) => c n * fourier n (y : 𝕋))
    (g' := fun (n : ℤ) (y : ℝ) => dcf c n * fourier n (y : 𝕋)) (y₀ := 0) hu
    (fun n y => by
      have h := (hasDerivAt_fourier (1:ℝ) n y).const_mul (c n)
      refine h.congr_deriv ?_
      simp only [dcf]; push_cast; ring)
    (fun n y => by rw [norm_mul, norm_fourier_pt, mul_one])
    (by
      refine Summable.of_norm ?_
      simpa [norm_fourier_pt] using hc.summable) s
  exact this

lemma contDiff_ser_nat (k : ℕ) : ∀ c : ℤ → ℂ, Rapid c → ContDiff ℝ k (ser c) := by
  induction k with
  | zero =>
    intro c hc
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_tsum (fun n => continuous_const.mul
      ((fourier n).continuous.comp (AddCircle.continuous_mk' (1:ℝ)))) hc.summable
      (fun n x => by rw [norm_mul, norm_fourier_pt, mul_one])
  | succ k ih =>
    intro c hc
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun s => (hasDerivAt_ser hc s).differentiableAt, by simp, ?_⟩
    have : deriv (ser c) = ser (dcf c) := funext fun s => (hasDerivAt_ser hc s).deriv
    rw [this]
    exact ih _ hc.d

lemma contDiff_ser {c : ℤ → ℂ} (hc : Rapid c) : ContDiff ℝ (⊤ : ℕ∞) (ser c) :=
  contDiff_infty.2 fun k => contDiff_ser_nat k c hc

/-- Gaussian-type weights are rapidly decaying -/
lemma summable_pow_gauss (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℤ => (|(n : ℝ)|) ^ k * Real.exp (-(a * (n : ℝ) ^ 2)) := by
  have hr : Real.exp (-a) < 1 := by simpa using ha
  have hs : Summable fun m : ℕ => ((m : ℝ)) ^ k * Real.exp (-a) ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])
  have h1 : Summable fun m : ℕ => (|((m : ℤ) : ℝ)|) ^ k * Real.exp (-(a * ((m : ℤ) : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
    simp only [Int.cast_natCast, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h
        nlinarith
    nlinarith
  refine Summable.of_nat_of_neg h1 ?_
  refine h1.congr fun m => ?_
  simp

lemma Rapid.of_gauss {a : ℝ} (ha : 0 < a) {c : ℤ → ℂ} {M : ℝ}
    (hM : ∀ n, ‖c n‖ ≤ M * Real.exp (-(a * (n : ℝ) ^ 2))) : Rapid c := by
  intro k
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_pow_gauss k ha).mul_left M)
  calc (|(n : ℝ)|) ^ k * ‖c n‖ ≤ (|(n : ℝ)|) ^ k * (M * Real.exp (-(a * (n : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left (hM n) (by positivity)
    _ = M * ((|(n : ℝ)|) ^ k * Real.exp (-(a * (n : ℝ) ^ 2))) := by ring

end MarkovTriple.BGL.Circle
