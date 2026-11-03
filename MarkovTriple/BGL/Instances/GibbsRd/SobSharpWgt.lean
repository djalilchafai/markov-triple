import MarkovTriple.BGL.Instances.GibbsRd.SobSharpBound

/-!
# Integrability of `(1 + |ξ|)^m |𝓕 F|` (R17 SobSharp)

Comparison `(1+|ξ|)^{2k} ≤ C wgt_k(ξ)`, Cauchy–Schwarz in the form `ab ≤ (a² + b²)/2` with
`a = (1+|ξ|)^{-(k-m)} ∈ L²` (exactly when `2(k-m) > d`) and `b = (1+|ξ|)^k |𝓕 F| ∈ L²`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff FourierTransform ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem norm_pow_le (k : ℕ) (hk : 1 ≤ k) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖ξ‖ ^ (2 * k) ≤ (d : ℝ) ^ k * ∑ i, (ξ i) ^ (2 * k) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : ‖ξ‖ = 0 := by simp [Subsingleton.elim ξ 0]
    rw [this]
    simp [Nat.pos_iff_ne_zero.mp (by omega : 0 < 2 * k)]
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have h1 := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => (ξ i) ^ 2) (fun i _ => sq_nonneg _) n
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ‖ξ‖ ^ 2 = ∑ i, (ξ i) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have h3 : (∑ i, (ξ i) ^ 2) ^ (n + 1) / (d : ℝ) ^ n ≤ ∑ i, (ξ i) ^ (2 * (n + 1)) := by
      refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [← pow_mul]
    rw [div_le_iff₀ (by positivity)] at h3
    calc ‖ξ‖ ^ (2 * (n + 1)) = (‖ξ‖ ^ 2) ^ (n + 1) := by rw [← pow_mul]
      _ = (∑ i, (ξ i) ^ 2) ^ (n + 1) := by rw [h2]
      _ ≤ (∑ i, (ξ i) ^ (2 * (n + 1))) * (d : ℝ) ^ n := h3
      _ ≤ (∑ i, (ξ i) ^ (2 * (n + 1))) * (d : ℝ) ^ (n + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun i _ => (even_two_mul _).pow_nonneg _)
          exact pow_le_pow_right₀ (by exact_mod_cast hd) (Nat.le_succ n)
      _ = _ := by ring

theorem one_add_pow_le (k : ℕ) (r : ℝ) (hr : 0 ≤ r) : (1 + r) ^ (2 * k) ≤ 2 ^ (2 * k) * (1 + r ^ (2 * k)) := by
  rcases le_total r 1 with h | h
  · calc (1 + r) ^ (2 * k) ≤ 2 ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ _ := by
          have : 0 ≤ r ^ (2 * k) := pow_nonneg hr _
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2 * k)]
  · calc (1 + r) ^ (2 * k) ≤ (2 * r) ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = 2 ^ (2 * k) * r ^ (2 * k) := mul_pow _ _ _
      _ ≤ _ := by
          have : 0 ≤ r ^ (2 * k) := pow_nonneg hr _
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2 * k)]

theorem one_add_norm_pow_le_wgt (k : ℕ) (hk : 1 ≤ k) (ξ : EuclideanSpace ℝ (Fin d)) :
    (1 + ‖ξ‖) ^ (2 * k) ≤ (2 ^ (2 * k) * (1 + (d : ℝ) ^ k)) * wgt d k ξ := by
  have h1 := one_add_pow_le k ‖ξ‖ (norm_nonneg _)
  have h2 := norm_pow_le k hk ξ
  set S : ℝ := ∑ i, (ξ i) ^ (2 * k) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (even_two_mul _).pow_nonneg _
  have hw : 1 + S ≤ wgt d k ξ := by
    unfold wgt
    have : S ≤ ∑ i, (2 * Real.pi * ξ i) ^ (2 * k) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_pow]
      have : (1 : ℝ) ≤ (2 * Real.pi) ^ (2 * k) :=
        one_le_pow₀ (by nlinarith [Real.pi_gt_three])
      have h0 : 0 ≤ (ξ i) ^ (2 * k) := (even_two_mul _).pow_nonneg _
      nlinarith
    linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ k := by positivity
  have h2pos : (0 : ℝ) < 2 ^ (2 * k) := by positivity
  calc (1 + ‖ξ‖) ^ (2 * k) ≤ 2 ^ (2 * k) * (1 + ‖ξ‖ ^ (2 * k)) := h1
    _ ≤ 2 ^ (2 * k) * (1 + (d : ℝ) ^ k * S) := by gcongr
    _ ≤ 2 ^ (2 * k) * ((1 + (d : ℝ) ^ k) * (1 + S)) := by
        gcongr
        nlinarith [mul_nonneg hd0 hS0]
    _ ≤ 2 ^ (2 * k) * ((1 + (d : ℝ) ^ k) * wgt d k ξ) := by gcongr
    _ = _ := by ring

theorem integrable_wgt_hat {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0) {F : (Fin d → ℝ) → ℝ}
    (hF0 : ∀ᵐ x, x ∉ K0 → F x = 0) (hF2 : MemLp F 2) (hF1 : Integrable F) (k : ℕ)
    {G : Fin d → (Fin d → ℝ) → ℝ} (hW : ∀ i, WeakIter (List.replicate k i) F (G i))
    (hG2 : ∀ i, MemLp (G i) 2) (hG1 : ∀ i, Integrable (G i)) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2) := by
  have hcont : Continuous (fun ξ : EuclideanSpace ℝ (Fin d) => wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2) := by
    have : Continuous (fun ξ : EuclideanSpace ℝ (Fin d) => wgt d k ξ) := by
      unfold wgt
      fun_prop
    exact this.mul ((continuous_hat hF1).norm.pow 2)
  have h := wgt_hat_lintegral_le hK0 hF0 hF2 hF1 k hW hG2 hG1
  refine (lintegral_ofReal_ne_top_iff_integrable hcont.aestronglyMeasurable
    (Eventually.of_forall fun ξ => mul_nonneg (wgt_pos k ξ).le (sq_nonneg _))).1 ?_
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

theorem integrable_weighted_hat {F : (Fin d → ℝ) → ℝ} (hF1 : Integrable F) (m k : ℕ)
    (hk : d + 2 * m < 2 * k)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2)) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖) ^ m * ‖𝓕 (lft F) ξ‖) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = m + t := ⟨k - m, by omega⟩
  have hk1 : 1 ≤ m + t := by omega
  set C : ℝ := 2 ^ (2 * (m + t)) * (1 + (d : ℝ) ^ (m + t)) with hC
  have hcH : Continuous (𝓕 (lft F)) := continuous_hat hF1
  have hA : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => (((1 + ‖ξ‖) ^ t)⁻¹) ^ 2) := by
    have h := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin d)) (μ := volume)
      (r := ((2 * t : ℕ) : ℝ)) (by
        rw [finrank_euclideanSpace_fin]
        exact_mod_cast (by omega : d < 2 * t))
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    have h0 : (0 : ℝ) ≤ 1 + ‖ξ‖ := by positivity
    simp only
    rw [Real.rpow_neg h0, Real.rpow_natCast, inv_pow, ← pow_mul, mul_comm t 2]
  have hB : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => C * (wgt d (m + t) ξ * ‖𝓕 (lft F) ξ‖ ^ 2)) :=
    hint.const_mul C
  have hsum := (hA.add hB).div_const 2
  refine hsum.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_const.add continuous_norm).pow m |>.mul hcH.norm).aestronglyMeasurable
  · set r : ℝ := ‖ξ‖ with hr
    have h0 : (0 : ℝ) < 1 + r := by positivity
    set a : ℝ := ((1 + r) ^ t)⁻¹ with ha
    set b : ℝ := (1 + r) ^ (m + t) * ‖𝓕 (lft F) ξ‖ with hb
    have hab : (1 + r) ^ m * ‖𝓕 (lft F) ξ‖ = a * b := by
      simp only [ha, hb, pow_add]
      field_simp
    have hb2 : b ^ 2 ≤ C * (wgt d (m + t) ξ * ‖𝓕 (lft F) ξ‖ ^ 2) := by
      have := one_add_norm_pow_le_wgt (d := d) (m + t) hk1 ξ
      have h1 : b ^ 2 = (1 + r) ^ (2 * (m + t)) * ‖𝓕 (lft F) ξ‖ ^ 2 := by
        simp only [hb]; rw [mul_pow, ← pow_mul, mul_comm (m + t) 2]
      rw [h1]
      calc _ ≤ (C * wgt d (m + t) ξ) * ‖𝓕 (lft F) ξ‖ ^ 2 :=
            mul_le_mul_of_nonneg_right this (sq_nonneg _)
        _ = _ := by ring
    have hnn : 0 ≤ (1 + r) ^ m * ‖𝓕 (lft F) ξ‖ := by positivity
    rw [Real.norm_of_nonneg hnn, hab]
    show a * b ≤ (a ^ 2 + C * (wgt d (m + t) ξ * ‖𝓕 (lft F) ξ‖ ^ 2)) / 2
    nlinarith [sq_nonneg (a - b)]

end MarkovTriple.BGL.Instances.GibbsRd.Sob
