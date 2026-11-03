import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.CurvSum

/-!
# Pure finite-sum algebra behind the Bochner formula (index gymnastics at a point)

Arrays over `Fin d` (no calculus): `g` the co-metric (symmetric), `c m k i` Christoffel symbols.
-/


namespace MarkovTriple.BGL.Instances.Riemannian

variable {d : ℕ}

/-- Leibniz rule for the carré du champ, algebra (the derivative index `k` is fixed). -/
lemma alg_G1 (g : Fin d → Fin d → ℝ) (c : Fin d → Fin d → Fin d → ℝ) (u v U V : Fin d → ℝ)
    (k : Fin d) :
    (∑ i, ∑ j, (-∑ m, (c i k m * g m j + c j k m * g i m)) * u i * v j) +
      ∑ i, ∑ j, g i j * (U i * v j + u i * V j) =
    ∑ i, ∑ j, g i j * ((U i - ∑ m, c m k i * u m) * v j + u i * (V j - ∑ m, c m k j * v m)) := by
  have a1 : ∑ i, ∑ j, ∑ m, c i k m * g m j * u i * v j =
      ∑ i, ∑ j, ∑ m, g i j * (c m k i * u m * v j) := by
    sums3
  have a2 : ∑ i, ∑ j, ∑ m, c j k m * g i m * u i * v j =
      ∑ i, ∑ j, ∑ m, g i j * (u i * (c m k j * v m)) := by
    sums3
  simp only [mul_sub, sub_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith [a1, a2]

/-- algebra of `Hess Γ(f) = 2 g^{ab} ∇_iH_{ja} f_b + 2 g^{ab} H_{ja} H_{ib}` (row `i` of the derivative fixed). -/
lemma alg_C2 (g : Fin d → Fin d → ℝ) (c : Fin d → Fin d → Fin d → ℝ) (dg : Fin d → Fin d → ℝ)
    (H : Fin d → Fin d → ℝ) (dH F f1 : Fin d → ℝ) (i j : Fin d)
    (hdg : ∀ a b, dg a b = -∑ m, (c a i m * g m b + c b i m * g a m))
    (hH : ∀ b, H i b = F b - ∑ m, c m i b * f1 m) :
    2 * ∑ a, ∑ b, ((dg a b * H j a + g a b * dH a) * f1 b + g a b * H j a * F b) -
      ∑ m, c m i j * (2 * ∑ a, ∑ b, g a b * H m a * f1 b) =
    2 * ∑ a, ∑ b, g a b * (dH a - ∑ m, c m i j * H m a - ∑ m, c m i a * H j m) * f1 b +
      2 * ∑ a, ∑ b, g a b * H j a * H i b := by
  simp only [hdg, hH, mul_sub, sub_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_neg]
  have e1 : ∑ x, ∑ x_1, ∑ i_1, 2 * (c x i i_1 * g i_1 x_1 * H j x * f1 x_1) =
      ∑ x, ∑ x_1, ∑ i_1, 2 * (g x x_1 * (c i_1 i x * H j i_1) * f1 x_1) := by sums3
  have e2 : ∑ x, ∑ x_1, ∑ i_1, 2 * (c x_1 i i_1 * g x i_1 * H j x * f1 x_1) =
      ∑ x, ∑ x_1, ∑ i_1, 2 * (g x x_1 * H j x * (c i_1 i x_1 * f1 i_1)) := by sums3
  have e3 : ∑ x, ∑ x_1, ∑ i_1, c x i j * (2 * (g x_1 i_1 * H x x_1 * f1 i_1)) =
      ∑ x, ∑ x_1, ∑ i_1, 2 * (g x x_1 * (c i_1 i j * H i_1 x) * f1 x_1) := by sums3
  linarith [e1, e2, e3]

/-- algebra of `∂_k (g^{ij} H_{ij}) = g^{ij} ∇_k H_{ij}` -/
lemma alg_G3 (g : Fin d → Fin d → ℝ) (c : Fin d → Fin d → Fin d → ℝ) (dg H dH : Fin d → Fin d → ℝ)
    (k : Fin d) (hdg : ∀ i j, dg i j = -∑ m, (c i k m * g m j + c j k m * g i m)) :
    ∑ i, ∑ j, (dg i j * H i j + g i j * dH i j) =
    ∑ i, ∑ j, g i j * (dH i j - ∑ m, c m k i * H m j - ∑ m, c m k j * H i m) := by
  simp only [hdg, mul_sub, add_mul, Finset.mul_sum, Finset.sum_mul, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ x, ∑ x_1, ∑ i, c x k i * g i x_1 * H x x_1 =
      ∑ x, ∑ x_1, ∑ i, g x x_1 * (c i k x * H i x_1) := by sums3
  have e2 : ∑ x, ∑ x_1, ∑ i, c x_1 k i * g x i * H x x_1 =
      ∑ x, ∑ x_1, ∑ i, g x x_1 * (c i k x_1 * H x i) := by sums3
  linarith [e1, e2]

/-- the Ricci identity, algebra: `∇_iH_{aj} − ∇_aH_{ij} = − R_{ia}{}^p{}_j f_p` -/
lemma alg_D (c : Fin d → Fin d → Fin d → ℝ) (dc : Fin d → Fin d → Fin d → Fin d → ℝ)
    (F H : Fin d → Fin d → ℝ) (f1 : Fin d → ℝ) (U3 dH : Fin d → Fin d → Fin d → ℝ)
    (hcs : ∀ m i a, c m i a = c m a i)
    (hU : ∀ i a j, U3 i a j = U3 a i j)
    (hH : ∀ i j, H i j = F i j - ∑ p, c p i j * f1 p)
    (hdH : ∀ i j a, dH i j a = U3 i j a - ∑ p, (dc i p j a * f1 p + c p j a * F i p))
    (i a j : Fin d) :
    (dH i a j - ∑ m, c m i a * H m j - ∑ m, c m i j * H a m) -
      (dH a i j - ∑ m, c m a i * H m j - ∑ m, c m a j * H i m) =
    -∑ p, (dc i p a j - dc a p i j + ∑ m, (c p i m * c m a j - c p a m * c m i j)) * f1 p := by
  simp only [hdH, hH, mul_sub, sub_mul, add_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e4 : ∑ x, c x i a * F x j = ∑ x, c x a i * F x j :=
    Finset.sum_congr rfl fun x _ => by rw [hcs x i a]
  have e5 : ∑ x, ∑ i_1, c x i a * (c i_1 x j * f1 i_1) = ∑ x, ∑ i_1, c x a i * (c i_1 x j * f1 i_1) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hcs x i a]
  have e6 : ∑ x, ∑ i_1, c x i j * (c i_1 a x * f1 i_1) =
      ∑ x, ∑ i_1, c x a i_1 * c i_1 i j * f1 x := by sums2
  have e7 : ∑ x, ∑ i_1, c x a j * (c i_1 i x * f1 i_1) =
      ∑ x, ∑ i_1, c x i i_1 * c i_1 a j * f1 x := by sums2
  linarith [e4, e5, e6, e7, hU i a j]

/-- assembly of the Bochner identity, algebra -/
lemma alg_assemble (g H HW : Fin d → Fin d → ℝ) (T : Fin d → Fin d → Fin d → ℝ) (f1 Wd : Fin d → ℝ)
    (hg : ∀ i j, g i j = g j i) (hH : ∀ i j, H i j = H j i) :
    (1 / 2) * (∑ i, ∑ j, g i j * (2 * ∑ a, ∑ b, g a b * T i j a * f1 b +
          2 * ∑ a, ∑ b, g a b * H j a * H i b) -
        ∑ i, ∑ j, g i j * Wd i * (2 * ∑ a, ∑ b, g a b * H j a * f1 b)) -
      ∑ k, ∑ l, g k l * f1 k * (∑ i, ∑ j, g i j * T l i j -
        ∑ i, ∑ j, g i j * (HW l i * f1 j + Wd i * H l j)) =
    ∑ i, ∑ j, ∑ k, ∑ l, g i k * g j l * H i j * H k l +
      ∑ a, ∑ b, g a b * f1 b * ∑ i, ∑ j, g i j * (T i j a - T a i j) +
      ∑ k, ∑ l, ∑ i, ∑ j, g k l * f1 k * g i j * HW l i * f1 j := by
  simp only [mul_sub, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have eA1 : ∑ x, ∑ x_1, ∑ x_2, ∑ i, 1 / 2 * (g x x_1 * (2 * (g x_2 i * T x x_1 x_2 * f1 i))) =
      ∑ x, ∑ x_1, ∑ x_2, ∑ i, g x x_1 * f1 x_1 * (g x_2 i * T x_2 i x) := by sums4
  have eA2 : ∑ x, ∑ x_1, ∑ x_2, ∑ i, 1 / 2 * (g x x_1 * (2 * (g x_2 i * H x_1 x_2 * H x i))) =
      ∑ i, ∑ j, ∑ k, ∑ l, g i k * g j l * H i j * H k l := by sums4s [hg, hH]
  have eA3 : ∑ x, ∑ x_1, ∑ x_2, ∑ i, 1 / 2 * (g x x_1 * Wd x * (2 * (g x_2 i * H x_1 x_2 * f1 i))) =
      ∑ x, ∑ x_1, ∑ x_2, ∑ i, g x x_1 * f1 x * (g x_2 i * (Wd x_2 * H x_1 i)) := by sums4s [hg, hH]
  have eB1 : ∑ x, ∑ x_1, ∑ x_2, ∑ i, g x x_1 * f1 x * (g x_2 i * T x_1 x_2 i) =
      ∑ x, ∑ x_1, ∑ x_2, ∑ i, g x x_1 * f1 x_1 * (g x_2 i * T x x_2 i) := by sums4s [hg, hH]
  have eB2 : ∑ x, ∑ x_1, ∑ x_2, ∑ i, g x x_1 * f1 x * (g x_2 i * (HW x_1 x_2 * f1 i)) =
      ∑ k, ∑ l, ∑ i, ∑ j, g k l * f1 k * g i j * HW l i * f1 j := by sums4
  linarith [eA1, eA2, eA3, eB1, eB2]

end MarkovTriple.BGL.Instances.Riemannian
