import Mathlib

/-!
# Fischer decomposition of homogeneous polynomials (Round 29, stream N, group N2)

Purely algebraic (`MvPolynomial (Fin n) ℝ`): every homogeneous polynomial of degree `d` is a finite sum
`Σ_j |x|^{2j} h_j` of harmonic homogeneous polynomials `h_j` of degree `d - 2j` (BGL §2.7 / classical).
Proof by strong induction on `d`: `Δ(|x|² q) = (2n + 4 deg q) q + |x|² Δ q`, hence `Δ(|x|^{2j+2} h) = a_j |x|^{2j} h`
with `a_j > 0` for harmonic `h`.  See `STATEMENTS_R29_N.md`.
-/

open MvPolynomial

namespace MarkovTriple.BGL.SphereN

variable {n : ℕ}

abbrev Pn (n : ℕ) := MvPolynomial (Fin n) ℝ

noncomputable def lap (p : Pn n) : Pn n := ∑ i, pderiv i (pderiv i p)

noncomputable def rsq : Pn n := ∑ i, X i * X i

def IsHarm (k : ℕ) (p : Pn n) : Prop := p.IsHomogeneous k ∧ lap p = 0

lemma lap_add (p q : Pn n) : lap (p + q) = lap p + lap q := by
  simp [lap, Finset.sum_add_distrib]

lemma lap_zero : lap (0 : Pn n) = 0 := by simp [lap]

lemma lap_smul (c : ℝ) (p : Pn n) : lap (c • p) = c • lap p := by
  simp [lap, Finset.smul_sum]

lemma lap_sub (p q : Pn n) : lap (p - q) = lap p - lap q := by
  simp [lap, Finset.sum_sub_distrib]

lemma lap_mul (p q : Pn n) :
    lap (p * q) = lap p * q + 2 * ∑ i, pderiv i p * pderiv i q + p * lap q := by
  unfold lap
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pderiv_mul, map_add]; ring

lemma pderiv_rsq (i : Fin n) : pderiv i (rsq : Pn n) = 2 * X i := by
  classical
  have h : ∀ j, pderiv i (X j * X j : Pn n) = if j = i then 2 * X j else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [pderiv_mul, pderiv_X_self, ite_true]; ring
    · simp [pderiv_X_of_ne hj, hj]
  simp [rsq, h]

lemma lap_rsq : lap (rsq : Pn n) = 2 * (n : Pn n) := by
  have h : ∀ i : Fin n, pderiv i (2 * X i : Pn n) = 2 := by
    intro i
    rw [(map_ofNat C 2).symm, pderiv_C_mul, pderiv_X_self, mul_one]
  simp only [lap, pderiv_rsq, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma sum_pderiv_rsq (q : Pn n) :
    ∑ i, pderiv i (rsq : Pn n) * pderiv i q = 2 * ∑ i, X i * pderiv i q := by
  simp only [pderiv_rsq, Finset.mul_sum, mul_assoc]

lemma lap_rsq_mul (q : Pn n) :
    lap (rsq * q) = 2 * (n : Pn n) * q + 4 * ∑ i, X i * pderiv i q + rsq * lap q := by
  rw [lap_mul, lap_rsq, sum_pderiv_rsq]
  ring

lemma lap_rsq_mul_hom {d : ℕ} {q : Pn n} (hq : q.IsHomogeneous d) :
    lap (rsq * q) = (2 * (n : ℝ) + 4 * d) • q + rsq * lap q := by
  rw [lap_rsq_mul, hq.sum_X_mul_pderiv]
  simp only [smul_eq_C_mul, nsmul_eq_mul, map_add, map_mul, map_natCast, map_ofNat]
  ring

lemma isHomogeneous_rsq : (rsq : Pn n).IsHomogeneous 2 := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  exact (isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ i)

lemma pderiv_hom_zero {p : Pn n} (hp : p.IsHomogeneous 0) (i : Fin n) : pderiv i p = 0 := by
  ext m
  rw [coeff_pderiv]
  have : p.coeff (m + Finsupp.single i 1) = 0 := by
    apply hp.coeff_eq_zero
    rw [Finsupp.degree_eq_weight_one, map_add]
    have h3 : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) (Finsupp.single i 1 : Fin n →₀ ℕ) = 1 := by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [h3]
    omega
  rw [this, zero_mul]
  simp

lemma pderiv_hom_succ {d : ℕ} {p : Pn n} (hp : p.IsHomogeneous (d + 1)) (i : Fin n) :
    (pderiv i p).IsHomogeneous d := by
  intro m hm
  rw [coeff_pderiv] at hm
  have h1 : p.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hm
  have h2 := hp h1
  have h3 : Finsupp.weight 1 (Finsupp.single i 1 : Fin n →₀ ℕ) = 1 := by
    simp [Finsupp.weight_apply, Finsupp.sum_single_index]
  rw [map_add, h3] at h2
  omega

lemma lap_hom_zero_of_lt {d : ℕ} (hd : d < 2) {p : Pn n} (hp : p.IsHomogeneous d) : lap p = 0 := by
  interval_cases d
  · simp [lap, pderiv_hom_zero hp]
  · simp only [lap]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [pderiv_hom_zero (pderiv_hom_succ hp i)]

lemma lap_hom {d : ℕ} {p : Pn n} (hp : p.IsHomogeneous (d + 2)) : (lap p).IsHomogeneous d :=
  IsHomogeneous.sum _ _ _ fun i _ => pderiv_hom_succ (pderiv_hom_succ hp i) i

lemma isHomogeneous_rsq_pow_mul {j k : ℕ} {h : Pn n} (hh : h.IsHomogeneous k) :
    ((rsq : Pn n) ^ j * h).IsHomogeneous (2 * j + k) :=
  (isHomogeneous_rsq.pow j).mul hh

/-- `Δ (|x|^{2j+2} h) = a_j |x|^{2j} h` with `a_j > 0` for harmonic `h`. -/
lemma lap_rsq_pow_mul_harm (hn : 0 < n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) (j : ℕ) :
    ∃ a : ℝ, 0 < a ∧ lap ((rsq : Pn n) ^ (j + 1) * h) = a • ((rsq : Pn n) ^ j * h) := by
  induction j with
  | zero =>
    refine ⟨2 * n + 4 * k, by positivity, ?_⟩
    rw [pow_one, lap_rsq_mul_hom hh.1, hh.2]
    simp
  | succ j ih =>
    obtain ⟨a, ha, hj⟩ := ih
    refine ⟨(2 * n + 4 * ((2 * (j + 1) + k : ℕ) : ℝ)) + a, by positivity, ?_⟩
    have hq := isHomogeneous_rsq_pow_mul (j := j + 1) hh.1
    have e : (rsq : Pn n) ^ (j + 1 + 1) * h = rsq * (rsq ^ (j + 1) * h) := by ring
    have e1 : (rsq : Pn n) ^ (j + 1) * h = rsq * (rsq ^ j * h) := by ring
    rw [e, lap_rsq_mul_hom hq, hj, mul_smul_comm, e1]
    module

/-- the span of the `|x|^{2j} h`, `h` harmonic homogeneous of degree `d - 2j`. -/
noncomputable def Wsp (n d : ℕ) : Submodule ℝ (Pn n) :=
  Submodule.span ℝ {q | ∃ (j k : ℕ) (h : Pn n), IsHarm k h ∧ k + 2 * j = d ∧ q = rsq ^ j * h}

lemma Wsp_hom {d : ℕ} {q : Pn n} (hq : q ∈ Wsp n d) : q.IsHomogeneous d := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨j, k, h, hh, hk, rfl⟩
    have := isHomogeneous_rsq_pow_mul (j := j) hh.1
    rwa [show 2 * j + k = d by omega] at this
  · exact isHomogeneous_zero (σ := Fin n) (R := ℝ) d
  · intro x y _ _ hx hy; exact hx.add hy
  · intro c x _ hx; rw [smul_eq_C_mul]; exact hx.C_mul c

/-- **Fischer decomposition.** -/
theorem fischer (hn : 0 < n) : ∀ (d : ℕ) {p : Pn n}, p.IsHomogeneous d → p ∈ Wsp n d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro p hp
    by_cases hd : d < 2
    · refine Submodule.subset_span ⟨0, d, p, ⟨hp, lap_hom_zero_of_lt hd hp⟩, by simp, by simp⟩
    · obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
      have hl : lap p ∈ Wsp n e := ih e (by omega) (lap_hom hp)
      -- solve `Δ q = Δ p` with `q ∈ Wsp (e+2)` of the form `|x|² · (…)`
      have key : ∀ w ∈ Wsp n e, ∃ q ∈ Wsp n (e + 2), lap q = w := by
        intro w hw
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
        · rintro _ ⟨j, k, h, hh, hk, rfl⟩
          obtain ⟨a, ha, hl'⟩ := lap_rsq_pow_mul_harm hn hh j
          refine ⟨a⁻¹ • (rsq ^ (j + 1) * h), ?_, ?_⟩
          · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j + 1, k, h, hh, by omega, rfl⟩)
          · rw [lap_smul, hl', smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
        · exact ⟨0, Submodule.zero_mem _, lap_zero⟩
        · rintro x y _ _ ⟨qx, hqx, rfl⟩ ⟨qy, hqy, rfl⟩
          exact ⟨qx + qy, Submodule.add_mem _ hqx hqy, lap_add _ _⟩
        · rintro c x _ ⟨qx, hqx, rfl⟩
          exact ⟨c • qx, Submodule.smul_mem _ _ hqx, lap_smul _ _⟩
      obtain ⟨q, hq, hql⟩ := key _ hl
      have hqh := Wsp_hom hq
      have hharm : IsHarm (e + 2) (p - q) := ⟨hp.sub hqh, by rw [lap_sub, hql, sub_self]⟩
      have : p = (p - q) + q := by ring
      rw [this]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨0, e + 2, p - q, hharm, by simp, by simp⟩) hq

end MarkovTriple.BGL.SphereN
