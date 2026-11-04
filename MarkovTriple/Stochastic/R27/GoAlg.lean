import Mathlib

/-!
# Round 27 (K), part 2a: the algebra of the Gegenbauer operator on polynomials

`M p = (1 - X²) p'' - 4 X p'` acts on `ℝ[X]` triangularly: `coeff_k (M p) = (k+2)(k+1) p_{k+2} - k(k+3) p_k`.  Hence
`(M + n(n+3))` maps polynomials of degree `≤ n` to degree `< n`, and `∏_{j<N} (M + j(j+3))` kills `degreeLT N`.
The abstract lemma `exists_eigen_decomp`: if `ι : V → H` intertwines `M` with operators whose eigenvectors are `P_t`-eigenvectors
and `∏_{j<N}(M + μ_j) p = 0` with `μ_j` distinct, then `P_t ι p = ι q` for some `q`.
-/

open Polynomial Finset

namespace MarkovTriple.Stochastic.R27

/-- `M p = (1 - X²) p'' - 4 X p'`. -/
noncomputable def goM : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := (1 - X ^ 2) * derivative (derivative p) - 4 * X * derivative p
  map_add' p q := by simp only [derivative_add]; ring
  map_smul' c p := by
    simp only [derivative_smul, RingHom.id_apply, smul_sub, mul_smul_comm]

lemma goM_apply (p : ℝ[X]) :
    goM p = (1 - X ^ 2) * derivative (derivative p) - 4 * X * derivative p := rfl

lemma coeff_derivative2 (p : ℝ[X]) (k : ℕ) :
    (derivative (derivative p)).coeff k = ((k : ℝ) + 2) * ((k : ℝ) + 1) * p.coeff (k + 2) := by
  rw [coeff_derivative, coeff_derivative]; push_cast; ring

lemma coeff_goM (p : ℝ[X]) (k : ℕ) :
    (goM p).coeff k = ((k : ℝ) + 2) * ((k : ℝ) + 1) * p.coeff (k + 2) - (k : ℝ) * ((k : ℝ) + 3) * p.coeff k := by
  have h : goM p = derivative (derivative p) - X ^ 2 * derivative (derivative p) - C 4 * (X * derivative p) := by
    rw [goM_apply]; simp only [map_ofNat]; ring
  rw [h, coeff_sub, coeff_sub, coeff_C_mul, coeff_derivative2]
  rcases k with _ | _ | k
  · simp [coeff_derivative]
  · simp [coeff_X_pow_mul', coeff_X_mul, coeff_derivative]
    norm_num
  · have e : (k + 1 + 1 : ℕ) = k + 2 := rfl
    simp only [coeff_X_pow_mul', Nat.le_add_left, ↓reduceIte, coeff_X_mul, coeff_derivative, e]
    push_cast
    ring_nf

/-- `∏_{j<n} (Y + μ_j)` -/
noncomputable def chi (μ : ℕ → ℝ) (n : ℕ) : ℝ[X] := ∏ j ∈ range n, (X + C (μ j))

lemma chi_succ (μ : ℕ → ℝ) (n : ℕ) : chi μ (n + 1) = (X + C (μ n)) * chi μ n := by
  rw [chi, chi, prod_range_succ, mul_comm]

section Abstract

variable {V H : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup H] [Module ℝ H]

lemma aeval_chi_succ (M : V →ₗ[ℝ] V) (μ : ℕ → ℝ) (n : ℕ) (p : V) :
    aeval M (chi μ (n + 1)) p = M (aeval M (chi μ n) p) + μ n • aeval M (chi μ n) p := by
  rw [chi_succ, map_mul, Module.End.mul_apply]
  simp [Module.algebraMap_end_apply]

lemma aeval_chi_succ' (M : V →ₗ[ℝ] V) (μ : ℕ → ℝ) (n : ℕ) (p : V) :
    aeval M (chi μ (n + 1)) p = aeval M (chi μ n) (M p + μ n • p) := by
  rw [chi, prod_range_succ, map_mul, Module.End.mul_apply]
  simp [Module.algebraMap_end_apply, chi]

/-- **Finite spectral decomposition on a polynomially-annihilated vector**: if `∏_{j<n}(M + μ_j)` kills `p` (`μ` injective),
and `Pt` maps each `M`-eigenvector (eigenvalue `-μ_j`) of the form `q` to the range of `ι`, then `Pt (ι p)` is in the range of `ι`. -/
theorem exists_eigen_decomp (M : V →ₗ[ℝ] V) (ι : V →ₗ[ℝ] H) (Pt : H →ₗ[ℝ] H) (μ : ℕ → ℝ)
    (hμ : Function.Injective μ)
    (heig : ∀ (j : ℕ) (q : V), M q = (-μ j) • q → Pt (ι q) ∈ LinearMap.range ι) :
    ∀ (n : ℕ) (p : V), aeval M (chi μ n) p = 0 → Pt (ι p) ∈ LinearMap.range ι := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have : p = 0 := by simpa [chi] using hp
    subst this
    simp
  | succ n ih =>
    intro p hp
    set r := aeval M (chi μ n) p with hr
    have hMr : M r = (-μ n) • r := by
      have := aeval_chi_succ M μ n p
      rw [hp, ← hr] at this
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left this.symm
    set D := (chi μ n).eval (-μ n) with hD
    have hD0 : D ≠ 0 := by
      rw [hD, chi, eval_prod]
      refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
      simp only [eval_add, eval_X, eval_C]
      intro h
      have : μ j = μ n := by linarith
      have := hμ this
      simp [this] at hj
    have hDr : aeval M (chi μ n) r = D • r :=
      Module.End.aeval_apply_of_mem_apply_eq_smul hMr
    have hp' : aeval M (chi μ n) (p - D⁻¹ • r) = 0 := by
      rw [map_sub, map_smul, hDr, ← hr, smul_smul, inv_mul_cancel₀ hD0, one_smul, sub_self]
    have h1 := ih _ hp'
    have h2 := heig n r hMr
    have : p = (p - D⁻¹ • r) + D⁻¹ • r := by abel
    rw [this, map_add, map_add, map_smul, map_smul]
    exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

end Abstract

/-- `(M + n(n+3))` lowers the degree of a polynomial of degree `≤ n`. -/
lemma degree_goM_add_lt (n : ℕ) {p : ℝ[X]} (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    (goM p + ((n : ℝ) * ((n : ℝ) + 3)) • p).degree < (n : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero] at hp ⊢
  intro m hm
  have hm' : n ≤ m := by exact_mod_cast hm
  simp only [coeff_add, coeff_smul, coeff_goM, smul_eq_mul]
  rcases eq_or_lt_of_le hm' with h | h
  · have h' : m = n := h.symm
    subst h'
    rw [hp (m + 2) (by exact_mod_cast (by omega : m + 1 ≤ m + 2))]
    ring
  · rw [hp (m + 2) (by exact_mod_cast (by omega : n + 1 ≤ m + 2)),
      hp m (by exact_mod_cast (by omega : n + 1 ≤ m))]
    ring

/-- the eigenvalues `n(n+3)` -/
noncomputable def goMu (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 3)

lemma goMu_injective : Function.Injective goMu := by
  intro a b h
  simp only [goMu] at h
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have : (a : ℝ) = b := by nlinarith
  exact_mod_cast this

lemma goMu_nonneg (n : ℕ) : 0 ≤ goMu n := by
  unfold goMu; positivity

/-- `∏_{j<n}(M + j(j+3))` kills the polynomials of degree `< n`. -/
theorem aeval_chi_goM (n : ℕ) : ∀ p : ℝ[X], p.degree < (n : WithBot ℕ) → aeval goM (chi goMu n) p = 0 := by
  induction n with
  | zero =>
    intro p hp
    have : p = 0 := by
      rw [degree_lt_iff_coeff_zero] at hp
      ext m; simpa using hp m (by simp)
    subst this
    simp
  | succ n ih =>
    intro p hp
    rw [aeval_chi_succ']
    refine ih _ ?_
    have h := degree_goM_add_lt n hp
    simpa [goMu] using h

end MarkovTriple.Stochastic.R27
