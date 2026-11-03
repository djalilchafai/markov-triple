import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE2B

/-!
# E2, pointwise (algebraic) estimates of Evans §6.3.1 Thm 1 Step 2

`pw_main`: ellipticity + Young for the leading term; `pw_R2`: Young for the commutator term.
Statement: `STATEMENTS_R16_E2.md`, E2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

/-- bilinear form of a matrix -/
def qf (M : Fin d → Fin d → ℝ) (ξ η : Fin d → ℝ) : ℝ := ∑ i, ∑ j, M i j * ξ i * η j

lemma qf_symm {M : Fin d → Fin d → ℝ} (hs : ∀ i j, M i j = M j i) (ξ η : Fin d → ℝ) :
    qf M η ξ = qf M ξ η := by
  unfold qf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hs j i]; ring

lemma qf_young {M : Fin d → Fin d → ℝ} (hs : ∀ i j, M i j = M j i) (hp : ∀ v, 0 ≤ qf M v v)
    (ξ η : Fin d → ℝ) : (1 / 2) * qf M ξ ξ - 2 * qf M η η ≤ qf M ξ ξ + 2 * qf M ξ η := by
  have h := hp (fun i => ξ i + 2 * η i)
  have e : qf M (fun i => ξ i + 2 * η i) (fun i => ξ i + 2 * η i) =
      qf M ξ ξ + 2 * qf M ξ η + 2 * qf M η ξ + 4 * qf M η η := by
    unfold qf
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, qf_symm hs ξ η] at h
  linarith

/-- the elementary absorption argument (Young, with explicit constants) -/
lemma final_arith {P N R1 R2 a K1 K2 Gs H0 N0 WΛ : ℝ} (ha : 0 < a) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hWΛ : 0 ≤ WΛ) (hN : N ≤ N0) (hP : 0 ≤ P)
    (h1 : a / 2 * P ≤ R1 + R2 + WΛ * N)
    (h2 : ∀ ε : ℝ, 0 < ε → R2 ≤ K1 * (ε * P + (1 / (4 * ε) + 1) * Gs + N))
    (h3 : ∀ ε : ℝ, 0 < ε → R1 ≤ ε * (2 * K2 * P + 8 * K2 * N) + H0 / (4 * ε)) :
    P ≤ 4 / a * (K1 * ((1 / (4 * (a / (8 * (K1 + 1)))) + 1) * Gs + N0) + (a / (16 * (K2 + 1))) * 8 * K2 * N0
      + H0 / (4 * (a / (16 * (K2 + 1)))) + WΛ * N0) := by
  set ε := a / (8 * (K1 + 1)) with hε
  set ε' := a / (16 * (K2 + 1)) with hε'
  have hεp : 0 < ε := by positivity
  have hε'p : 0 < ε' := by positivity
  have e1 : K1 * ε ≤ a / 8 := by
    rw [hε, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e2 : ε' * (2 * K2) ≤ a / 8 := by
    rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have i2 := h2 ε hεp
  have i3 := h3 ε' hε'p
  have hKN : K1 * N ≤ K1 * N0 := mul_le_mul_of_nonneg_left hN hK1
  have hK2N : ε' * (8 * K2 * N) ≤ ε' * (8 * K2 * N0) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN (by positivity)) hε'p.le
  have hWN : WΛ * N ≤ WΛ * N0 := mul_le_mul_of_nonneg_left hN hWΛ
  have t1 : K1 * (ε * P) ≤ a / 8 * P := by nlinarith
  have t2 : ε' * (2 * K2 * P) ≤ a / 8 * P := by nlinarith
  have : a / 4 * P ≤ K1 * ((1 / (4 * ε) + 1) * Gs + N0) + ε' * 8 * K2 * N0 + H0 / (4 * ε') + WΛ * N0 := by
    nlinarith
  have h4 : P ≤ 4 / a * (a / 4 * P) := by
    field_simp; exact le_refl _
  calc P ≤ 4 / a * (a / 4 * P) := h4
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith

namespace EllData
variable (E : EllData d)

/-- **pointwise main estimate**: the leading term `qf(A(y)) (ξ, ξ + 2η) ≥ (λm/2)|ξ|² − 2WΛ|η|²`. -/
lemma pw_main {S : Set (Rd d)} {lam m W Λ : ℝ} (hlam : ∀ y ∈ S, ∀ ξ : Rd d, lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, E.a i j y * ξ i * ξ j)
    (hm : ∀ y ∈ S, m ≤ E.w y) (hW : ∀ y ∈ S, E.w y ≤ W) (hΛ : ∀ y ∈ S, ∀ (v : Rd d), ∑ i, ∑ j, E.a i j y * v i * v j ≤ Λ * ∑ i, v i ^ 2)
    (hlam0 : 0 ≤ lam)
    (y : Rd d) (ξ η : Rd d) (hy : y ∈ S ∨ ((∀ i, ξ i = 0) ∧ ∀ j, η j = 0)) :
    (lam * m / 2) * ∑ i, ξ i ^ 2 - 2 * W * Λ * ∑ i, η i ^ 2 ≤
      ∑ i, ∑ j, (E.w y * E.a i j y) * ξ i * ξ j + 2 * ∑ i, ∑ j, (E.w y * E.a i j y) * ξ i * η j := by
  rcases hy with hy | ⟨h1, h2⟩
  · set M : Fin d → Fin d → ℝ := fun i j => E.w y * E.a i j y with hM
    have hs : ∀ i j, M i j = M j i := fun i j => by simp only [hM, E.a_symm i j y]
    have hqM : ∀ v, qf M v v = E.w y * ∑ i, ∑ j, E.a i j y * v i * v j := fun v => by
      simp only [qf, hM, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hp : ∀ v, 0 ≤ qf M v v := fun v => by
      rw [hqM]; exact mul_nonneg (E.w_pos y).le (E.quad_nonneg v y)
    have hy1 := qf_young hs hp ξ η
    have hxi : lam * m * ∑ i, ξ i ^ 2 ≤ qf M ξ ξ := by
      rw [hqM]
      have h1 := hlam y hy ξ
      have h2 := hm y hy
      have hS : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [mul_le_mul h2 h1 (by positivity) (E.w_pos y).le, mul_nonneg hlam0 hS]
    have heta : qf M η η ≤ W * Λ * ∑ i, η i ^ 2 := by
      rw [hqM]
      have hq0 := E.quad_nonneg η y
      have h1 := hΛ y hy η
      have h2 := hW y hy
      calc E.w y * ∑ i, ∑ j, E.a i j y * η i * η j ≤ W * ∑ i, ∑ j, E.a i j y * η i * η j :=
            mul_le_mul_of_nonneg_right h2 hq0
        _ ≤ W * (Λ * ∑ i, η i ^ 2) := mul_le_mul_of_nonneg_left h1 ((E.w_pos y).le.trans h2)
        _ = W * Λ * ∑ i, η i ^ 2 := by ring
    have : ∑ i, ∑ j, (E.w y * E.a i j y) * ξ i * ξ j = qf M ξ ξ := rfl
    have h' : ∑ i, ∑ j, (E.w y * E.a i j y) * ξ i * η j = qf M ξ η := rfl
    rw [this, h']
    nlinarith [hxi, heta, hy1]
  · have e1 : ∀ i, ξ i = 0 := h1
    have e2 : ∀ i, η i = 0 := h2
    simp [e1, e2]

/-- **pointwise commutator estimate** -/
lemma pw_R2 (g ξ η : Fin d → ℝ) (Dm : Fin d → Fin d → ℝ) (ζ B Bz ε : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (hBz : 0 ≤ Bz)
    (hD : ζ ≠ 0 → ∀ i j, |Dm i j| ≤ B) (hz : |ζ| ≤ Bz) :
    |∑ i, ∑ j, g i * Dm i j * (ζ * ξ j + 2 * ζ * η j)| ≤
      B * Bz * d * (ε * ∑ j, ξ j ^ 2 + (1 / (4 * ε) + 1) * ∑ i, g i ^ 2 + ∑ j, η j ^ 2) := by
  by_cases hζ : ζ = 0
  · simp only [hζ, zero_mul, add_zero, mul_zero, Finset.sum_const_zero, abs_zero]
    positivity
  have hD' := hD hζ
  have hterm : ∀ i j, |g i * Dm i j * (ζ * ξ j + 2 * ζ * η j)| ≤
      B * Bz * (ε * ξ j ^ 2 + (1 / (4 * ε) + 1) * g i ^ 2 + η j ^ 2) := by
    intro i j
    have h1 : |g i * Dm i j * (ζ * ξ j + 2 * ζ * η j)| ≤ B * Bz * (|g i| * (|ξ j| + 2 * |η j|)) := by
      rw [abs_mul, abs_mul]
      have : |ζ * ξ j + 2 * ζ * η j| ≤ Bz * (|ξ j| + 2 * |η j|) := by
        calc |ζ * ξ j + 2 * ζ * η j| ≤ |ζ * ξ j| + |2 * ζ * η j| := abs_add_le _ _
          _ = |ζ| * (|ξ j| + 2 * |η j|) := by
              rw [abs_mul, abs_mul, abs_mul]; simp only [abs_two]; ring
          _ ≤ Bz * (|ξ j| + 2 * |η j|) := mul_le_mul_of_nonneg_right hz (by positivity)
      calc |g i| * |Dm i j| * |ζ * ξ j + 2 * ζ * η j| ≤ |g i| * B * (Bz * (|ξ j| + 2 * |η j|)) := by
            gcongr; exact hD' i j
        _ = B * Bz * (|g i| * (|ξ j| + 2 * |η j|)) := by ring
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB hBz)
    have a1 : |g i| * |ξ j| ≤ ε * ξ j ^ 2 + (1 / (4 * ε)) * g i ^ 2 := by
      have key : 4 * ε * (|g i| * |ξ j|) ≤ 4 * ε ^ 2 * ξ j ^ 2 + g i ^ 2 := by
        nlinarith [sq_nonneg (2 * ε * |ξ j| - |g i|), sq_abs (ξ j), sq_abs (g i)]
      have e : ε * ξ j ^ 2 + (1 / (4 * ε)) * g i ^ 2 = (4 * ε ^ 2 * ξ j ^ 2 + g i ^ 2) / (4 * ε) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      linarith
    have a2 : 2 * (|g i| * |η j|) ≤ g i ^ 2 + η j ^ 2 := by
      nlinarith [sq_nonneg (|g i| - |η j|), sq_abs (g i), sq_abs (η j)]
    nlinarith [a1, a2]
  calc |∑ i, ∑ j, g i * Dm i j * (ζ * ξ j + 2 * ζ * η j)|
      ≤ ∑ i, ∑ j, |g i * Dm i j * (ζ * ξ j + 2 * ζ * η j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, B * Bz * (ε * ξ j ^ 2 + (1 / (4 * ε) + 1) * g i ^ 2 + η j ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = B * Bz * d * (ε * ∑ j, ξ j ^ 2 + (1 / (4 * ε) + 1) * ∑ i, g i ^ 2 + ∑ j, η j ^ 2) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
