import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Full.Orth

/-!
# Sup bound for harmonic homogeneous polynomials (Round 32, stream Y, step 1)

BGL §2.2 / C.5.  Without the mean value property: the identity `Σ_i ∫_S (∂_i h)² = k(2k+n-2) ∫_S h²` (Green on the sphere
and the extrinsic formula) together with Euler's identity and Cauchy-Schwarz gives, by induction on the degree,
`h(y)² ≤ |y|^{2k} n^k ∫_S h²`.
-/

open MeasureTheory MvPolynomial

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma restr_pderiv (i : Fin n) (h : Pn n) (x : Sph n) :
    restr (MvPolynomial.pderiv i h) x = dd i (ev h) (cv (x : Ee n)) := by
  rw [dd_evP]; rfl

lemma integrable_restr_sq (hn : 1 ≤ n) (p q : Pn n) :
    Integrable (fun x => restr p x * restr q x) (σ n) := by
  have := σ_isProbabilityMeasure hn
  exact (memLp_of_mem (mul_mem (restr_mem p) (restr_mem q)) 1).integrable le_rfl

theorem harm_grad_L2 (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) :
    ∑ i, ∫ x, (restr (MvPolynomial.pderiv i h) x)^2 ∂σ n
      = (k : ℝ) * (2 * k + n - 2) * ∫ x, (restr h x)^2 ∂σ n := by
  have h1 := ibp_sphere (n := n) (Nat.one_le_of_lt hn) (restr_mem h) (restr_mem h)
  rw [LS_restr_harm hh] at h1
  have hG : ∀ x, ΓS (restr h) (restr h) x
      = ∑ i, (restr (MvPolynomial.pderiv i h) x)^2 - (k : ℝ)^2 * (restr h x)^2 := by
    intro x
    have e := ΓS_extrinsic (Sm_ev h) (Sm_ev h) x
    have e1 : (fun z : Sph n => ev h (cv (z : Ee n))) = restr h := rfl
    rw [e1] at e
    rw [e, euler_ev hh.1]
    simp only [restr_pderiv]
    have : ev h (cv (x : Ee n)) = restr h x := rfl
    rw [this]
    simp only [pow_two]; ring
  have hint : ∀ i, Integrable (fun x => (restr (MvPolynomial.pderiv i h) x)^2) (σ n) := fun i => by
    simpa [pow_two] using integrable_restr_sq (Nat.one_le_of_lt hn) (MvPolynomial.pderiv i h) (MvPolynomial.pderiv i h)
  have hint2 : Integrable (fun x => (restr h x)^2) (σ n) := by
    simpa [pow_two] using integrable_restr_sq (Nat.one_le_of_lt hn) h h
  have hL : ∫ x, restr h x * (-((k : ℝ) * (k + n - 2)) * restr h x) ∂σ n
      = -((k : ℝ) * (k + n - 2)) * ∫ x, (restr h x)^2 ∂σ n := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [hL] at h1
  have hG2 : ∫ x, ΓS (restr h) (restr h) x ∂σ n
      = ∑ i, ∫ x, (restr (MvPolynomial.pderiv i h) x)^2 ∂σ n - (k : ℝ)^2 * ∫ x, (restr h x)^2 ∂σ n := by
    simp only [hG]
    rw [integral_sub (integrable_finsetSum _ fun i _ => hint i) (hint2.const_mul _),
      integral_finsetSum _ fun i _ => hint i, integral_const_mul]
  have : ∑ i, ∫ x, (restr (MvPolynomial.pderiv i h) x)^2 ∂σ n
      = ((k : ℝ) * (k + n - 2) + (k : ℝ)^2) * ∫ x, (restr h x)^2 ∂σ n := by
    linarith
  rw [this]; ring

lemma pderiv_comm' (i j : Fin n) (p : Pn n) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  ext m
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  have e : m + Finsupp.single i 1 + Finsupp.single j 1 = m + Finsupp.single j 1 + Finsupp.single i 1 :=
    add_right_comm _ _ _
  rw [e]
  by_cases hij : i = j
  · subst hij; rfl
  · simp only [Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij, ite_false, add_zero]
    ring

lemma isHarm_pderiv {k : ℕ} {h : Pn n} (hh : IsHarm (k + 1) h) (i : Fin n) :
    IsHarm k (MvPolynomial.pderiv i h) := by
  refine ⟨pderiv_hom_succ hh.1 i, ?_⟩
  have : lap (MvPolynomial.pderiv i h) = MvPolynomial.pderiv i (lap h) := by
    unfold lap
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_comm' j i h, pderiv_comm' j i (MvPolynomial.pderiv j h)]
  rw [this, hh.2]; simp

/-- the squared `L²(σ)` norm of the restriction. -/
noncomputable def Nn (n : ℕ) (h : Pn n) : ℝ := ∫ x, (restr h x)^2 ∂σ n

lemma Nn_nonneg (h : Pn n) : 0 ≤ Nn n h := integral_nonneg fun _ => sq_nonneg _

theorem harm_sup (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) (y : Fin n → ℝ) :
    (ev h y)^2 ≤ nrm y ^ (2 * k) * (n : ℝ) ^ k * ∫ x, (restr h x)^2 ∂σ n := by
  induction k generalizing h with
  | zero =>
    have h0 : h.totalDegree = 0 := by
      have := hh.1.totalDegree_le
      omega
    have hC := (totalDegree_eq_zero_iff_eq_C).1 h0
    have := σ_isProbabilityMeasure (Nat.one_le_of_lt hn)
    have e : ∀ x : Sph n, restr h x = h.coeff 0 := fun x => by
      rw [hC]; simp [restr]
    have e2 : ∀ z, ev h z = h.coeff 0 := fun z => by
      rw [hC]; simp [ev]
    simp [e, e2]
  | succ k ih =>
    have hg : ∀ i, IsHarm k (MvPolynomial.pderiv i h) := fun i => isHarm_pderiv hh i
    have hE := euler_ev hh.1 y
    have hcs : ((k + 1 : ℕ) * ev h y)^2 ≤ nrm y ^ 2 * ∑ i, (ev (MvPolynomial.pderiv i h) y)^2 := by
      rw [← hE, nrm_sq]
      simp only [dd_evP]
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y (fun i => ev (MvPolynomial.pderiv i h) y)
      simpa [LebesgueRd.sq] using this
    have hsum : ∑ i, (ev (MvPolynomial.pderiv i h) y)^2
        ≤ nrm y ^ (2 * k) * (n : ℝ) ^ k * ((k + 1 : ℕ) * (2 * (k + 1 : ℕ) + n - 2) * Nn n h) := by
      have := harm_grad_L2 hn hh
      calc ∑ i, (ev (MvPolynomial.pderiv i h) y)^2
          ≤ ∑ i, nrm y ^ (2 * k) * (n : ℝ) ^ k * Nn n (MvPolynomial.pderiv i h) :=
            Finset.sum_le_sum fun i _ => ih (hg i)
        _ = nrm y ^ (2 * k) * (n : ℝ) ^ k * ∑ i, Nn n (MvPolynomial.pderiv i h) := by
            rw [Finset.mul_sum]
        _ = _ := by
            rw [show ∑ i, Nn n (MvPolynomial.pderiv i h)
              = ((k + 1 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + n - 2) * Nn n h from by simpa [Nn] using this]
    have hN := Nn_nonneg h
    have hr : 0 ≤ nrm y := nrm_nonneg y
    have hK : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    set K : ℝ := ((k + 1 : ℕ) : ℝ) with hKdef
    set e : ℝ := (ev h y)^2 with he
    set P : ℝ := nrm y ^ (2 * k) * (n : ℝ) ^ k with hP
    have hP0 : 0 ≤ P := by positivity
    have h1 : K ^ 2 * e ≤ nrm y ^ 2 * (P * (K * (2 * K + n - 2) * Nn n h)) := by
      calc K ^ 2 * e = (K * ev h y) ^ 2 := by rw [he]; ring
        _ ≤ nrm y ^ 2 * ∑ i, (ev (MvPolynomial.pderiv i h) y)^2 := hcs
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : 2 * K + n - 2 ≤ K * n := by nlinarith
    have h3 : K ^ 2 * e ≤ nrm y ^ 2 * (P * (K * (K * n) * Nn n h)) := by
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hP0) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by linarith)) hN
    have h4 : e ≤ nrm y ^ 2 * (P * (n * Nn n h)) := by
      have hK2 : 0 < K ^ 2 := by positivity
      refine le_of_mul_le_mul_left ?_ hK2
      calc K ^ 2 * e ≤ _ := h3
        _ = K ^ 2 * (nrm y ^ 2 * (P * (n * Nn n h))) := by ring
    calc e ≤ _ := h4
      _ = nrm y ^ (2 * (k + 1)) * (n : ℝ) ^ (k + 1) * Nn n h := by rw [hP]; ring

end MarkovTriple.BGL.SphereN
