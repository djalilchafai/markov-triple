import Mathlib
import MarkovTriple.Stochastic.R32A2.Hfun

/-!
# Round 32 (A2), part 4: uniform bounds for the radial cut-offs `cut R` under linear growth of `∇V`

`|L cut_R| ≤ K`, `|∂ᵢ cut_R| ≤ K` uniformly in `R ≥ 1` (only linear growth of `∇V` is used, not `BddHess3`), and vanishing on `{qd < R²}`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.Stochastic.R32A2

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

lemma cut_vanish' (G : GibbsRdData d) {R : ℝ} (hR : 0 < R) {y : Rd d} (hy : qd y < R ^ 2) :
    (∀ i, pderiv (cut R) i y = 0) ∧ Lr G.V (cut R) y = 0 := by
  have hU := isOpen_inner (d := d) R
  have h0 : ∀ z ∈ {x : Rd d | qd x < R ^ 2}, cut R z = 1 := fun z hz => cut_eq_one hR (le_of_lt hz)
  have h1 : ∀ z ∈ {x : Rd d | qd x < R ^ 2}, ∀ i, pderiv (cut R) i z = 0 := fun z hz i =>
    pderiv_eq_zero_of_open hU h0 hz i
  have h2 : ∀ z ∈ {x : Rd d | qd x < R ^ 2}, ∀ i j, pderiv (pderiv (cut R) i) j z = 0 := fun z hz i j =>
    pderiv_eq_zero_of_open hU (h1 · · i) hz j
  have hy' : y ∈ {x : Rd d | qd x < R ^ 2} := hy
  exact ⟨h1 y hy', by simp [Lr, h1 y hy', h2 y hy']⟩

/-- uniform bounds -/
lemma cut_bounds_lin (G : GibbsRdData d) {C : ℝ}
    (hC : ∀ (x : Rd d) (i : Fin d), |pderiv G.V i x| ≤ C * (1 + ∑ j, |x j|)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ y : Rd d, |Lr G.V (cut R) y| ≤ K ∧
      ∀ i, |pderiv (cut R) i y| ≤ K := by
  obtain ⟨B, hB0, hB⟩ := cut_deriv_bound (d := d)
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨B * (d + d * C'), by positivity, fun R hR y => ⟨?_, fun i => ?_⟩⟩
  · -- the first-derivative bounds
    have hR0 : 0 < R := by linarith
    have hl0 : 0 ≤ ∑ j, |y j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hp1 : ∀ i, |pderiv (cut R) i y| ≤ B := by
      intro i
      have := hB R hR [i] (by simp) y
      have h2 : (1 : ℝ) ≤ (1 + l1 y / R) ^ 2 := by
        have : 0 ≤ l1 y / R := div_nonneg (l1_nonneg y) hR0.le
        nlinarith
      simp only [List.length_singleton, pow_one] at this
      have e : dw [i] (cut R) y = pderiv (cut R) i y := rfl
      rw [e] at this
      calc |pderiv (cut R) i y| ≤ (1 + l1 y / R) ^ 2 * |pderiv (cut R) i y| :=
            le_mul_of_one_le_left (abs_nonneg _) h2
        _ ≤ B / R := this
        _ ≤ B := div_le_self hB0 hR
    have hp1' : ∀ i, |pderiv (cut R) i y| * (1 + ∑ j, |y j|) ≤ B := by
      intro i
      have := hB R hR [i] (by simp) y
      simp only [List.length_singleton, pow_one] at this
      have e : dw [i] (cut R) y = pderiv (cut R) i y := rfl
      rw [e] at this
      have hl : l1 y = ∑ j, |y j| := rfl
      rw [hl] at this
      have hq : 0 < 1 + (∑ j, |y j|) / R := by positivity
      have h3 : (1 + ∑ j, |y j|) ≤ R * (1 + (∑ j, |y j|) / R) := by
        rw [mul_add, mul_one, mul_div_cancel₀ _ hR0.ne']; linarith
      have h4 : |pderiv (cut R) i y| * (1 + (∑ j, |y j|) / R) ≤ B / R := by
        calc |pderiv (cut R) i y| * (1 + (∑ j, |y j|) / R)
            ≤ (1 + (∑ j, |y j|) / R) ^ 2 * |pderiv (cut R) i y| := by
              nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (pderiv (cut R) i y)) hq.le) (div_nonneg hl0 hR0.le)]
          _ ≤ B / R := this
      calc |pderiv (cut R) i y| * (1 + ∑ j, |y j|)
          ≤ |pderiv (cut R) i y| * (R * (1 + (∑ j, |y j|) / R)) :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = R * (|pderiv (cut R) i y| * (1 + (∑ j, |y j|) / R)) := by ring
        _ ≤ R * (B / R) := mul_le_mul_of_nonneg_left h4 hR0.le
        _ = B := by field_simp
    have hp2 : ∀ i, |pderiv (pderiv (cut R) i) i y| ≤ B := by
      intro i
      have := hB R hR [i, i] (by simp) y
      have h2 : (1 : ℝ) ≤ (1 + l1 y / R) ^ 2 := by
        have : 0 ≤ l1 y / R := div_nonneg (l1_nonneg y) hR0.le
        nlinarith
      have e : dw [i, i] (cut R) y = pderiv (pderiv (cut R) i) i y := rfl
      rw [e] at this
      simp only [List.length_cons, List.length_nil] at this
      calc |pderiv (pderiv (cut R) i) i y| ≤ (1 + l1 y / R) ^ 2 * |pderiv (pderiv (cut R) i) i y| :=
            le_mul_of_one_le_left (abs_nonneg _) h2
        _ ≤ B / R ^ (0 + 1 + 1) := this
        _ ≤ B := by
          have : (1 : ℝ) ≤ R ^ (0 + 1 + 1) := one_le_pow₀ hR
          exact div_le_self hB0 this
    unfold Lr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |pderiv (pderiv (cut R) i) i y - pderiv G.V i y * pderiv (cut R) i y|
        ≤ ∑ _i : Fin d, (B + C' * B) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (abs_sub _ _).trans ?_
          rw [abs_mul]
          have h5 : |pderiv G.V i y| * |pderiv (cut R) i y| ≤ C' * B := by
            calc |pderiv G.V i y| * |pderiv (cut R) i y|
                ≤ (C' * (1 + ∑ j, |y j|)) * |pderiv (cut R) i y| :=
                  mul_le_mul_of_nonneg_right ((hC y i).trans (mul_le_mul_of_nonneg_right
                    (le_max_left _ _) (by linarith))) (abs_nonneg _)
              _ = C' * (|pderiv (cut R) i y| * (1 + ∑ j, |y j|)) := by ring
              _ ≤ C' * B := mul_le_mul_of_nonneg_left (hp1' i) hC'0
          linarith [hp2 i]
      _ = B * (d + d * C') := by simp; ring
  · have hR0 : 0 < R := by linarith
    have := hB R hR [i] (by simp) y
    have h2 : (1 : ℝ) ≤ (1 + l1 y / R) ^ 2 := by
      have : 0 ≤ l1 y / R := div_nonneg (l1_nonneg y) hR0.le
      nlinarith
    simp only [List.length_singleton, pow_one] at this
    have e : dw [i] (cut R) y = pderiv (cut R) i y := rfl
    rw [e] at this
    have hBle : B ≤ B * (d + d * C') := by
      have hd : (1 : ℝ) ≤ d := by exact_mod_cast Fin.pos i
      have : (1 : ℝ) ≤ d + d * C' := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d) hC'0]
      nlinarith
    calc |pderiv (cut R) i y| ≤ (1 + l1 y / R) ^ 2 * |pderiv (cut R) i y| :=
          le_mul_of_one_le_left (abs_nonneg _) h2
      _ ≤ B / R := this
      _ ≤ B := div_le_self hB0 hR
      _ ≤ _ := hBle

end MarkovTriple.Stochastic.R32A2
