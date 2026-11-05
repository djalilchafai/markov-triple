import Mathlib
import MarkovTriple.BGL.Instances.SphereN.ExtrinsicL
import MarkovTriple.BGL.Instances.SphereN.Meas
import MarkovTriple.BGL.Instances.SphereN.Full.Fischer

/-!
# Polynomials on the sphere and the eigenvalue of harmonic polynomials (Round 29, stream N, group N2)

`restr p` is the restriction of a polynomial to `S^{n-1}`; it lies in `𝒜₀` (`restr_mem`);
for `h` harmonic and homogeneous of degree `k`, `L (restr h) = -k(k+n-2) restr h` (`LS_restr_harm`),
from the extrinsic formula `LS_extrinsic` and Euler's identity.
-/

open MvPolynomial MeasureTheory

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

/-- evaluation of a polynomial as a function on `ℝ^n`. -/
noncomputable def ev (p : Pn n) : (Fin n → ℝ) → ℝ := fun y => MvPolynomial.eval y p

noncomputable def restr (p : Pn n) : Sph n → ℝ := fun x => MvPolynomial.eval (cv (x : Ee n)) p

lemma Sm_ev (p : Pn n) : Sm (ev p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : ev (C a : Pn n) = fun _ => a := by funext y; simp [ev]
    rw [e]; exact contDiff_const
  | add p q hp hq =>
    have e : ev (p + q) = fun y => ev p y + ev q y := by funext y; simp [ev]
    rw [e]; exact hp.add hq
  | mul_X p i hp =>
    have e : ev (p * X i) = fun y => ev p y * y i := by funext y; simp [ev]
    rw [e]; exact hp.mul (contDiff_apply ℝ ℝ i)

lemma dd_coordP (i j : Fin n) (y : Fin n → ℝ) :
    dd i (fun z : Fin n → ℝ => z j) y = ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) := by
  classical
  have : HasFDerivAt (fun z : Fin n → ℝ => z j) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) y :=
    hasFDerivAt_apply j y
  unfold dd
  rw [this.fderiv]
  simp [Pi.single_apply]

lemma dd_evP (p : Pn n) (i : Fin n) : dd i (ev p) = ev (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : ev (C a : Pn n) = fun _ => a := by funext y; simp [ev]
    rw [this, dd_const]; funext y; simp [ev]
  | add p q hp hq =>
    have e : ev (p + q) = ev p + ev q := by funext y; simp [ev]
    rw [e, dd_add (Sm_ev p) (Sm_ev q), hp, hq]
    funext y; simp [ev]
  | mul_X p j hp =>
    have e : ev (p * X j) = ev p * (fun z : Fin n → ℝ => z j) := by funext y; simp [ev]
    rw [e]
    funext y
    rw [dd_mul (Sm_ev p) (contDiff_apply ℝ ℝ j), hp, dd_coordP, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
    have hs : MvPolynomial.eval y ((Pi.single i (1 : Pn n) : Fin n → Pn n) j) =
        (Pi.single i (1 : ℝ) : Fin n → ℝ) j := by
      by_cases hji : j = i <;> simp [hji]
    simp only [ev, map_add, map_mul, hs, eval_X]

lemma lap_evP (p : Pn n) : Lf (ev p) = ev (lap p) := by
  funext y
  simp only [Lf, dd_evP, lap, ev, map_sum]

lemma euler_ev {k : ℕ} {p : Pn n} (hp : p.IsHomogeneous k) (y : Fin n → ℝ) :
    ∑ i, y i * dd i (ev p) y = k * ev p y := by
  have := congrArg (MvPolynomial.eval y) hp.sum_X_mul_pderiv
  simpa [dd_evP, ev, map_sum, nsmul_eq_mul] using this

/-- polynomial form of the second Euler identity. -/
lemma sum_sum_euler {k : ℕ} {p : Pn n} (hp : p.IsHomogeneous k) :
    ∑ i, ∑ j, X i * X j * MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = ((k : ℝ) * k - k) • p := by
  classical
  have hE := hp.sum_X_mul_pderiv
  have h1 : ∀ i : Fin n, MvPolynomial.pderiv i p + ∑ j, X j * MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = (k : ℝ) • MvPolynomial.pderiv i p := by
    intro i
    have := congrArg (MvPolynomial.pderiv i) hE
    simp only [map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_nsmul] at this
    rw [Finset.sum_add_distrib] at this
    have e1 : ∑ j, ((Pi.single i (1 : Pn n) : Fin n → Pn n) j) * MvPolynomial.pderiv j p = MvPolynomial.pderiv i p := by
      simp [Pi.single_apply]
    rw [e1] at this
    rw [← Nat.cast_smul_eq_nsmul ℝ] at this
    exact this
  have h2 : ∑ i, X i * (MvPolynomial.pderiv i p + ∑ j, X j * MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) = (k : ℝ) • ∑ i, X i * MvPolynomial.pderiv i p := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i, mul_smul_comm]
  simp only [mul_add, Finset.sum_add_distrib, hE] at h2
  have e3 : ∑ i, ∑ j, X i * X j * MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = ∑ i, X i * ∑ j, X j * MvPolynomial.pderiv i (MvPolynomial.pderiv j p) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e3]
  rw [← Nat.cast_smul_eq_nsmul ℝ] at h2
  have : ∑ i, X i * ∑ j, X j * MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = (k : ℝ) • (k : ℝ) • p - (k : ℝ) • p := by
    rw [← h2]; abel
  rw [this]; module

lemma sum_sum_euler_ev {k : ℕ} {p : Pn n} (hp : p.IsHomogeneous k) (y : Fin n → ℝ) :
    ∑ i, ∑ j, y i * y j * dd i (dd j (ev p)) y = ((k : ℝ) * k - k) * ev p y := by
  have := congrArg (MvPolynomial.eval y) (sum_sum_euler hp)
  simpa [dd_evP, ev, map_sum, smul_eq_C_mul] using this

/-- restrictions of polynomials are smooth. -/
theorem restr_mem (p : Pn n) : restr p ∈ A₀S n :=
  A₀S_of_contDiff (F := ev p) (Sm_ev p)

lemma eval_rsq (y : Fin n → ℝ) : MvPolynomial.eval y (rsq : Pn n) = ∑ i, y i * y i := by
  simp [rsq]

theorem restr_rsq_mul (q : Pn n) : restr (rsq * q) = restr q := by
  funext x
  have h : ∑ i, cv (x : Ee n) i * cv (x : Ee n) i = 1 := by
    have h3 : LebesgueRd.sq (cv (x : Ee n)) = 1 := by rw [← nrm_sq, nrm_cv_sph]; norm_num
    simpa [LebesgueRd.sq, pow_two] using h3
  simp only [restr, map_mul, eval_rsq, h, one_mul]

/-- **Harmonic homogeneous polynomials restrict to eigenfunctions of `L`.** -/
theorem LS_restr_harm {k : ℕ} {h : Pn n} (hh : IsHarm k h) :
    LS (restr h) = fun x => -((k : ℝ) * (k + n - 2)) * restr h x := by
  funext x
  have e := LS_extrinsic (Sm_ev h) x
  have e1 : (fun z : Sph n => ev h (cv (z : Ee n))) = restr h := rfl
  rw [e1] at e
  rw [e]
  have h0 : Lf (ev h) (cv (x : Ee n)) = 0 := by
    rw [lap_evP, hh.2]; simp [ev]
  rw [h0, sum_sum_euler_ev hh.1, euler_ev hh.1]
  simp only [restr, ev]
  ring

end MarkovTriple.BGL.SphereN
