import Mathlib

/-!
# A Hessian inequality on the tangent space (Round 28, stream L, group L3)

For a symmetric `H` with `H y = w`, `|y| = 1`, `w ⊥ y`:
`Σ H_ij² ≥ 2 Σ w_i² + (tr H)²/(n-1)`.  (`PHP` is a symmetric form on the `(n-1)`-dimensional tangent space.)
Proof: `0 ≤ Σ (H_ij − λ P_ij − w_i y_j − y_i w_j)²` with `λ = tr H/(n-1)`, `P = I − y yᵀ`.
-/

open Finset

namespace MarkovTriple.BGL.SphereN

lemma hess_ineq {n : ℕ} (hn : 2 ≤ n) (H : Fin n → Fin n → ℝ) (y w : Fin n → ℝ)
    (hsym : ∀ i j, H i j = H j i) (hHy : ∀ i, ∑ j, H i j * y j = w i)
    (hy : ∑ i, y i ^ 2 = 1) (hwy : ∑ i, w i * y i = 0) :
    2 * ∑ i, w i ^ 2 + (∑ i, H i i) ^ 2 / ((n : ℝ) - 1) ≤ ∑ i, ∑ j, H i j ^ 2 := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set T := ∑ i, H i i with hT
  set lam := T / ((n : ℝ) - 1) with hlam
  let δ : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0
  let P : Fin n → Fin n → ℝ := fun i j => δ i j - y i * y j
  let M : Fin n → Fin n → ℝ := fun i j => H i j - lam * P i j - w i * y j - y i * w j
  have hnn : 0 ≤ ∑ i, ∑ j, M i j ^ 2 := sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have expand : ∀ i j, M i j ^ 2 = H i j ^ 2 + lam ^ 2 * (δ i j - 2 * (δ i j * (y i * y j)) + (y i) ^ 2 * (y j) ^ 2)
      + (w i) ^ 2 * (y j) ^ 2 + (y i) ^ 2 * (w j) ^ 2
      - 2 * lam * (H i j * δ i j - H i j * (y i * y j))
      - 2 * (H i j * (w i * y j)) - 2 * (H i j * (y i * w j))
      + 2 * lam * (δ i j * (w i * y j) - (y i * w i) * (y j * y j))
      + 2 * lam * (δ i j * (y i * w j) - (y i * y i) * (y j * w j))
      + 2 * ((w i * y i) * (w j * y j)) := fun i j => by
    have hd : δ i j ^ 2 = δ i j := by by_cases h : i = j <;> simp [δ, h]
    simp only [M, P]; nlinarith [hd]
  have s1 : ∑ i, ∑ j, δ i j = n := by simp [δ]
  have sδy : ∑ i, ∑ j, δ i j * (y i * y j) = 1 := by
    simp only [δ, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq, ← pow_two, hy]
  have syy : ∑ i, ∑ j, (y i) ^ 2 * (y j) ^ 2 = 1 := by
    rw [← Finset.sum_mul_sum, hy, one_mul]
  have sHδ : ∑ i, ∑ j, H i j * δ i j = T := by
    simp [δ, hT]
  have hyHy : ∑ i, ∑ j, H i j * (y i * y j) = 0 := by
    have : ∀ i, ∑ j, H i j * (y i * y j) = y i * w i := fun i => by
      rw [← hHy i, Finset.mul_sum]; exact sum_congr rfl fun j _ => by ring
    simp only [this]
    rw [← hwy]; exact sum_congr rfl fun i _ => by ring
  have sww : ∑ i, ∑ j, (w i) ^ 2 * (y j) ^ 2 = ∑ i, w i ^ 2 := by
    rw [← Finset.sum_mul_sum, hy, mul_one]
  have syw : ∑ i, ∑ j, (y i) ^ 2 * (w j) ^ 2 = ∑ i, w i ^ 2 := by
    rw [← Finset.sum_mul_sum, hy, one_mul]
  have sHw1 : ∑ i, ∑ j, H i j * (w i * y j) = ∑ i, w i ^ 2 := by
    have : ∀ i, ∑ j, H i j * (w i * y j) = w i ^ 2 := fun i => by
      have := hHy i
      calc ∑ j, H i j * (w i * y j) = w i * ∑ j, H i j * y j := by
            rw [Finset.mul_sum]; exact sum_congr rfl fun j _ => by ring
        _ = w i ^ 2 := by rw [this]; ring
    simp only [this]
  have sHw2 : ∑ i, ∑ j, H i j * (y i * w j) = ∑ i, w i ^ 2 := by
    rw [Finset.sum_comm]
    have : ∀ j, ∑ i, H i j * (y i * w j) = w j ^ 2 := fun j => by
      have := hHy j
      calc ∑ i, H i j * (y i * w j) = w j * ∑ i, H j i * y i := by
            rw [Finset.mul_sum]; exact sum_congr rfl fun i _ => by rw [hsym i j]; ring
        _ = w j ^ 2 := by rw [this]; ring
    simp only [this]
  have sP1 : ∑ i, ∑ j, δ i j * (w i * y j) = 0 := by
    simp only [δ, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq, hwy]
  have sP2 : ∑ i, ∑ j, (y i * w i) * (y j * y j) = 0 := by
    rw [← Finset.sum_mul_sum]
    have h1 : ∑ j, y j * y j = 1 := by rw [← hy]; exact sum_congr rfl fun j _ => by ring
    have h2 : ∑ i, y i * w i = 0 := by rw [← hwy]; exact sum_congr rfl fun i _ => by ring
    rw [h1, h2, zero_mul]
  have sP3 : ∑ i, ∑ j, δ i j * (y i * w j) = 0 := by
    simp only [δ, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq]
    rw [← hwy]; exact sum_congr rfl fun i _ => by ring
  have sP4 : ∑ i, ∑ j, (y i * y i) * (y j * w j) = 0 := by
    rw [← Finset.sum_mul_sum]
    have h1 : ∑ j, y j * y j = 1 := by rw [← hy]; exact sum_congr rfl fun j _ => by ring
    have h2 : ∑ j, y j * w j = 0 := by rw [← hwy]; exact sum_congr rfl fun i _ => by ring
    rw [h1, h2, mul_zero]
  have sww2 : ∑ i, ∑ j, ((w i * y i) * (w j * y j)) = 0 := by
    rw [← Finset.sum_mul_sum, hwy, zero_mul]
  have tot : ∑ i, ∑ j, M i j ^ 2 = ∑ i, ∑ j, H i j ^ 2 + lam ^ 2 * ((n : ℝ) - 2 * 1 + 1)
      + ∑ i, w i ^ 2 + ∑ i, w i ^ 2 - 2 * lam * (T - 0) - 2 * ∑ i, w i ^ 2 - 2 * ∑ i, w i ^ 2
      + 2 * lam * (0 - 0) + 2 * lam * (0 - 0) + 2 * 0 := by
    have hc : ∀ (c : ℝ) (F : Fin n → Fin n → ℝ), ∑ i, ∑ j, c * F i j = c * ∑ i, ∑ j, F i j := by
      intro c F; simp [Finset.mul_sum]
    simp only [expand, sum_add_distrib, sum_sub_distrib, hc]
    rw [s1, sδy, syy, sww, syw, sHδ, hyHy, sHw1, sHw2, sP1, sP2, sP3, sP4, sww2]
  rw [tot] at hnn
  have hl : lam ^ 2 * ((n : ℝ) - 1) = T ^ 2 / ((n : ℝ) - 1) := by
    rw [hlam]; field_simp
  have hl2 : lam * T = T ^ 2 / ((n : ℝ) - 1) := by rw [hlam]; ring
  nlinarith [hl, hl2]

end MarkovTriple.BGL.SphereN
