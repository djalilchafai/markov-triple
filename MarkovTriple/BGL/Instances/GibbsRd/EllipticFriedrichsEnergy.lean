import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsEq

/-!
# The uniform `H¹` bound for the mollified solutions (R16, Friedrichs step)

Statement E2 of `STATEMENTS_R16_Friedrichs.md` (Caccioppoli inequality for `v = ρ ⋆ u` with the commutator error, absorbed
by local ellipticity).  Evans §6.3.1 Step 1 (Caccioppoli, with `ζ²v` as test function), Gilbarg–Trudinger (8.28).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

section
variable {b : Fin d → Fin d → (Fin d → ℝ) → ℝ} {ψ φ : (Fin d → ℝ) → ℝ} {R : ℝ}

lemma int_of_zero_off {f : (Fin d → ℝ) → ℝ} (hc : Continuous f) (h : ∀ y, R < ‖y‖ → f y = 0) : Integrable f :=
  hc.integrable_of_hasCompactSupport (hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R) fun y hy =>
    h y (by simpa using hy))

/-- integration by parts for the divergence form operator -/
lemma ibp_Pop (hb : ∀ i j, Sm (b i j)) (hψ : Sm ψ) (hφ : Sm φ) (hφ0 : ∀ y, R < ‖y‖ → φ y = 0) :
    ∫ x, ψ x * Pop b φ x = - ∫ x, ∑ i, ∑ j, b i j x * pderiv ψ i x * pderiv φ j x := by
  have hH : ∀ i, Sm (fun y => ∑ j, b i j y * pderiv φ j y) := fun i =>
    ContDiff.sum fun j _ => (hb i j).mul (hφ.pderiv j)
  have hH0 : ∀ i y, R < ‖y‖ → (∑ j, b i j y * pderiv φ j y) = 0 := fun i y hy =>
    Finset.sum_eq_zero fun j _ => by simp [pderiv_zero_off hφ0 j y hy]
  have hHc : ∀ i, HasCompactSupport (fun y => ∑ j, b i j y * pderiv φ j y) := fun i =>
    hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R) fun y hy => hH0 i y (by simpa using hy)
  have e1 : ∀ i, ∫ x, ψ x * pderiv (fun y => ∑ j, b i j y * pderiv φ j y) i x =
      -∫ x, pderiv ψ i x * ∑ j, b i j x * pderiv φ j x := fun i => ibp_smooth hψ (hH i) (hHc i) i
  have hint : ∀ i, Integrable (fun x => ψ x * pderiv (fun y => ∑ j, b i j y * pderiv φ j y) i x) := fun i =>
    int_of_zero_off (R := R) (hψ.continuous.mul ((hH i).pderiv i).continuous)
      (fun y hy => by rw [pderiv_zero_off (hH0 i) i y hy]; simp)
  have hint2 : ∀ i, Integrable (fun x => pderiv ψ i x * ∑ j, b i j x * pderiv φ j x) := fun i =>
    int_of_zero_off (R := R) ((hψ.pderiv i).continuous.mul (hH i).continuous)
      (fun y hy => by rw [hH0 i y hy]; simp)
  have e2 : ∫ x, ψ x * Pop b φ x = ∑ i, ∫ x, ψ x * pderiv (fun y => ∑ j, b i j y * pderiv φ j y) i x := by
    unfold Pop
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ fun i _ => hint i
  rw [e2]
  simp_rw [e1]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hint2 i]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring


/-- the algebra behind the Caccioppoli trick (uses the symmetry of `b`) -/
lemma caccioppoli_alg (c : Fin d → Fin d → ℝ) (hsym : ∀ i j, c i j = c j i) (p r : Fin d → ℝ) (ζ v : ℝ) :
    ∑ i, ∑ j, c i j * p i * (ζ ^ 2 * p j + 2 * ζ * v * r j) =
      (∑ i, ∑ j, c i j * (ζ * p i + v * r i) * (ζ * p j + v * r j)) - v ^ 2 * ∑ i, ∑ j, c i j * r i * r j := by
  have hsw : ∑ i, ∑ j, c i j * r i * p j = ∑ i, ∑ j, c i j * p i * r j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hsym i j]; ring
  have e : ∀ i j, c i j * (ζ * p i + v * r i) * (ζ * p j + v * r j) =
      ζ ^ 2 * (c i j * p i * p j) + ζ * v * (c i j * p i * r j) + ζ * v * (c i j * r i * p j) +
        v ^ 2 * (c i j * r i * r j) := fun i j => by ring
  have e' : ∀ i j, c i j * p i * (ζ ^ 2 * p j + 2 * ζ * v * r j) =
      ζ ^ 2 * (c i j * p i * p j) + 2 * ζ * v * (c i j * p i * r j) := fun i j => by ring
  simp only [e, e', Finset.sum_add_distrib, ← Finset.mul_sum, hsw]
  ring

variable {ρ u F : (Fin d → ℝ) → ℝ} {C₁ : ℝ} {ζ : (Fin d → ℝ) → ℝ} {R₀ : ℝ}

/-- **E2b** the energy identity for `w = ζ ρ⋆u` (Caccioppoli, exact form) -/
theorem energy_identity (hb : ∀ i j, Sm (b i j)) (hsym : ∀ i j x, b i j x = b j i x) (hk : FrKer ρ C₁)
    (heven : ∀ x, ρ (-x) = ρ x) (hu : LocallyIntegrable u) (hF : LocallyIntegrable F)
    (veq : ∀ a : (Fin d → ℝ) → ℝ, Sm a → (∀ y, R₀ + 1 < ‖y‖ → a y = 0) → ∫ x, u x * Pop b a x = ∫ x, F x * a x)
    (hζ : Sm ζ) (hζ0 : ∀ y, R₀ < ‖y‖ → ζ y = 0) :
    ∫ x, ∑ i, ∑ j, b i j x * pderiv (fun y => ζ y * moll ρ u y) i x * pderiv (fun y => ζ y * moll ρ u y) j x
      = (∫ x, moll ρ u x ^ 2 * ∑ i, ∑ j, b i j x * pderiv ζ i x * pderiv ζ j x)
        - (∫ x, moll ρ F x * (ζ x * (ζ x * moll ρ u x)))
        - ∫ x, u x * Tcomm b ρ (fun y => ζ y * (ζ y * moll ρ u y)) x := by
  set v := moll ρ u with hv
  have hvS : Sm v := moll_contDiff hk.sm hk.cs hu
  have hVS : Sm (moll ρ F) := moll_contDiff hk.sm hk.cs hF
  set w : (Fin d → ℝ) → ℝ := fun y => ζ y * v y with hw
  have hwS : Sm w := hζ.mul hvS
  set φ : (Fin d → ℝ) → ℝ := fun y => ζ y * (ζ y * v y) with hφ
  have hφS : Sm φ := hζ.mul hwS
  have hφ0 : ∀ y, R₀ < ‖y‖ → φ y = 0 := fun y hy => by simp [hφ, hζ0 y hy]
  have hw0 : ∀ y, R₀ < ‖y‖ → w y = 0 := fun y hy => by simp [hw, hζ0 y hy]
  have h1 := test_eq hb hk heven hu hF hφS hφ0 veq
  rw [ibp_Pop hb hvS hφS hφ0] at h1
  -- pointwise algebra
  have hpt : ∀ x, ∑ i, ∑ j, b i j x * pderiv v i x * pderiv φ j x =
      (∑ i, ∑ j, b i j x * pderiv w i x * pderiv w j x) - v x ^ 2 * ∑ i, ∑ j, b i j x * pderiv ζ i x * pderiv ζ j x := by
    intro x
    have e1 : ∀ j, pderiv φ j x = ζ x ^ 2 * pderiv v j x + 2 * ζ x * v x * pderiv ζ j x := fun j => by
      simp only [hφ]
      rw [pderiv_mul' hζ hwS, pderiv_mul' hζ hvS]; simp only [hw]; ring
    have e2 : ∀ i, pderiv w i x = ζ x * pderiv v i x + v x * pderiv ζ i x := fun i => by
      simp only [hw]; rw [pderiv_mul' hζ hvS]; ring
    simp only [e1, e2]
    exact caccioppoli_alg (fun i j => b i j x) (fun i j => hsym i j x) _ _ _ _
  have hI1 : Integrable (fun x => ∑ i, ∑ j, b i j x * pderiv v i x * pderiv φ j x) := by
    refine int_of_zero_off (R := R₀) ?_ fun y hy => ?_
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (((hb i j).continuous.mul (hvS.pderiv i).continuous).mul (hφS.pderiv j).continuous)
    · exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by simp [pderiv_zero_off hφ0 j y hy]
  have hI2 : Integrable (fun x => ∑ i, ∑ j, b i j x * pderiv w i x * pderiv w j x) := by
    refine int_of_zero_off (R := R₀) ?_ fun y hy => ?_
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (((hb i j).continuous.mul (hwS.pderiv i).continuous).mul (hwS.pderiv j).continuous)
    · exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by simp [pderiv_zero_off hw0 j y hy]
  have hI3 : Integrable (fun x => v x ^ 2 * ∑ i, ∑ j, b i j x * pderiv ζ i x * pderiv ζ j x) := by
    refine int_of_zero_off (R := R₀) ?_ fun y hy => ?_
    · exact (hvS.continuous.pow 2).mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (((hb i j).continuous.mul (hζ.pderiv i).continuous).mul (hζ.pderiv j).continuous))
    · simp [pderiv_zero_off hζ0 _ y hy]
  have hsplit : ∫ x, ∑ i, ∑ j, b i j x * pderiv v i x * pderiv φ j x =
      (∫ x, ∑ i, ∑ j, b i j x * pderiv w i x * pderiv w j x) - ∫ x, v x ^ 2 * ∑ i, ∑ j, b i j x * pderiv ζ i x * pderiv ζ j x := by
    rw [← integral_sub hI2 hI3]
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [hsplit] at h1
  have hVφ : ∀ x, moll ρ F x * φ x = moll ρ F x * (ζ x * (ζ x * v x)) := fun x => rfl
  simp only [hVφ] at h1
  linarith


/-- Young's inequality for the pairing of two `L²` functions -/
lemma amgm_int {p q : (Fin d → ℝ) → ℝ} (hp : AEStronglyMeasurable p volume) (hq : AEStronglyMeasurable q volume)
    (hp2 : Integrable (fun x => p x ^ 2)) (hq2 : Integrable (fun x => q x ^ 2)) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => p x * q x) ∧
      |∫ x, p x * q x| ≤ η / 2 * (∫ x, p x ^ 2) + 1 / (2 * η) * ∫ x, q x ^ 2 := by
  have hpt : ∀ x, |p x * q x| ≤ η / 2 * p x ^ 2 + 1 / (2 * η) * q x ^ 2 := fun x => by
    have h1 : 2 * η * |p x * q x| ≤ η ^ 2 * p x ^ 2 + q x ^ 2 := by
      have := sq_nonneg (η * |p x| - |q x|)
      rw [abs_mul]
      nlinarith [sq_abs (p x), sq_abs (q x)]
    have h2 : η / 2 * p x ^ 2 + 1 / (2 * η) * q x ^ 2 = (η ^ 2 * p x ^ 2 + q x ^ 2) / (2 * η) := by
      field_simp
    rw [h2, le_div_iff₀ (by positivity)]
    linarith
  have hdom : Integrable (fun x => η / 2 * p x ^ 2 + 1 / (2 * η) * q x ^ 2) :=
    (hp2.const_mul _).add (hq2.const_mul _)
  have hint : Integrable (fun x => p x * q x) := by
    refine hdom.mono' (hp.mul hq) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hpt x
  refine ⟨hint, ?_⟩
  calc |∫ x, p x * q x| = ‖∫ x, p x * q x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, (η / 2 * p x ^ 2 + 1 / (2 * η) * q x ^ 2) :=
        norm_integral_le_of_norm_le hdom (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)
    _ = _ := by rw [integral_add (hp2.const_mul _) (hq2.const_mul _), integral_const_mul, integral_const_mul]

/-- Jensen: mollification does not increase the squared `L²` norm -/
lemma integral_sq_moll_le (hk : FrKer ρ C₁) {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    Integrable (fun x => moll ρ f x ^ 2) ∧ ∫ x, moll ρ f x ^ 2 ≤ ∫ x, f x ^ 2 := by
  obtain ⟨hmem, hN⟩ := moll_memLp_norm_le hk.sm hk.cs hk.nonneg hk.integral hf
  have hi : Integrable (fun x => moll ρ f x ^ 2) :=
    (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem
  refine ⟨hi, ?_⟩
  have e1 := N2_sq hmem
  have e2 := N2_sq hf
  have : N2 (moll ρ f) ^ 2 ≤ N2 f ^ 2 := by
    nlinarith [N2_nonneg (moll ρ f), N2_nonneg f]
  rw [e1, e2] at this
  simpa [sq] using this


/-- the final absorption argument, as pure real arithmetic -/
lemma absorb {lam CT Z M₁ M₂ η W Jv Ju JF JV E A B Cc T2 Φ : ℝ} (hlam : 0 < lam) (hCT0 : 0 ≤ CT)
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂) (hη : η = 2 * CT * Z ^ 2 / lam + 1) (hW0 : 0 ≤ W) (hJv0 : 0 ≤ Jv) (hJF0 : 0 ≤ JF)
    (hEll : lam * W ≤ E) (hE : E = A - B - Cc) (hA : A ≤ M₁ * Jv)
    (hB : |B| ≤ 1 / 2 * JV + 1 / 2 * (Z ^ 4 * Jv)) (hC : |Cc| ≤ η / 2 * Ju + 1 / (2 * η) * T2)
    (hT2 : T2 ≤ CT * Φ) (hΦ : Φ ≤ 2 * Z ^ 2 * W + 2 * Z ^ 2 * M₂ * Jv) (hvJ : Jv ≤ Ju) (hVJ : JV ≤ JF) :
    W ≤ 2 * (M₁ + 1 / 2 + Z ^ 4 / 2 + η / 2 + CT * Z ^ 2 * M₂ / η) / lam * (Ju + JF) := by
  have hηpos : 0 < η := by rw [hη]; positivity
  have hCTη : CT * Z ^ 2 / η ≤ lam / 2 := by
    rw [div_le_iff₀ hηpos]
    have : lam / 2 * η = CT * Z ^ 2 + lam / 2 := by rw [hη]; field_simp
    nlinarith
  have hT2' : 1 / (2 * η) * T2 ≤ CT * Z ^ 2 / η * W + CT * Z ^ 2 * M₂ / η * Jv := by
    calc 1 / (2 * η) * T2 ≤ 1 / (2 * η) * (CT * (2 * Z ^ 2 * W + 2 * Z ^ 2 * M₂ * Jv)) :=
          mul_le_mul_of_nonneg_left (hT2.trans (mul_le_mul_of_nonneg_left hΦ hCT0)) (by positivity)
      _ = _ := by field_simp
  have hWη : CT * Z ^ 2 / η * W ≤ lam / 2 * W := mul_le_mul_of_nonneg_right hCTη hW0
  have c1 : M₁ * Jv ≤ M₁ * Ju := mul_le_mul_of_nonneg_left hvJ hM₁0
  have c2 : Z ^ 4 / 2 * Jv ≤ Z ^ 4 / 2 * Ju := mul_le_mul_of_nonneg_left hvJ (by positivity)
  have c3 : CT * Z ^ 2 * M₂ / η * Jv ≤ CT * Z ^ 2 * M₂ / η * Ju :=
    mul_le_mul_of_nonneg_left hvJ (by positivity)
  have n1 := neg_le_of_abs_le hB
  have n2 := neg_le_of_abs_le hC
  have h1 : lam / 2 * W ≤ M₁ * Jv + (1 / 2 * JV + 1 / 2 * (Z ^ 4 * Jv)) + (η / 2 * Ju + CT * Z ^ 2 * M₂ / η * Jv) := by
    linarith
  have h2 : lam / 2 * W ≤ (M₁ + 1 / 2 + Z ^ 4 / 2 + η / 2 + CT * Z ^ 2 * M₂ / η) * (Ju + JF) := by
    have c4 : 0 ≤ (M₁ + Z ^ 4 / 2 + η / 2 + CT * Z ^ 2 * M₂ / η) * JF :=
      mul_nonneg (by positivity) hJF0
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
  nlinarith

lemma sq_le_of_norm_le {a Z : ℝ} (h : ‖a‖ ≤ Z) : a ^ 2 ≤ Z ^ 2 := by
  rw [Real.norm_eq_abs] at h
  nlinarith [sq_abs a, abs_nonneg a]

/-- pointwise: `Σⱼ (∂ⱼ(ζ²v))² ≤ 2Z² Σⱼ (∂ⱼ(ζv))² + 2 Z² M₂ v²` -/
lemma phi_pointwise {ζ v : (Fin d → ℝ) → ℝ} {Z M₂ : ℝ} (hζ : Sm ζ) (hvS : Sm v) (hZ : ∀ x, ‖ζ x‖ ≤ Z)
    (hM₂ : ∀ x, ‖∑ j, pderiv ζ j x ^ 2‖ ≤ M₂) (x : Fin d → ℝ) :
    ∑ j, pderiv (fun y => ζ y * (ζ y * v y)) j x ^ 2 ≤
      2 * Z ^ 2 * (∑ j, pderiv (fun y => ζ y * v y) j x ^ 2) + 2 * Z ^ 2 * M₂ * v x ^ 2 := by
  have h1 : ζ x ^ 2 ≤ Z ^ 2 := sq_le_of_norm_le (hZ x)
  have hwS : Sm (fun y => ζ y * v y) := hζ.mul hvS
  have e : ∀ j, pderiv (fun y => ζ y * (ζ y * v y)) j x =
      ζ x * pderiv (fun y => ζ y * v y) j x + ζ x * v x * pderiv ζ j x := fun j => by
    rw [pderiv_mul' hζ hwS]; ring
  have hs : ∀ j, pderiv (fun y => ζ y * (ζ y * v y)) j x ^ 2 ≤
      2 * Z ^ 2 * pderiv (fun y => ζ y * v y) j x ^ 2 + 2 * (Z ^ 2 * v x ^ 2) * pderiv ζ j x ^ 2 := by
    intro j
    rw [e j]
    have a1 : (ζ x * pderiv (fun y => ζ y * v y) j x) ^ 2 ≤ Z ^ 2 * pderiv (fun y => ζ y * v y) j x ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have a2 : (ζ x * v x * pderiv ζ j x) ^ 2 ≤ Z ^ 2 * v x ^ 2 * pderiv ζ j x ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) (sq_nonneg _)
    nlinarith [sq_nonneg (ζ x * pderiv (fun y => ζ y * v y) j x - ζ x * v x * pderiv ζ j x)]
  calc _ ≤ ∑ j, (2 * Z ^ 2 * pderiv (fun y => ζ y * v y) j x ^ 2 + 2 * (Z ^ 2 * v x ^ 2) * pderiv ζ j x ^ 2) :=
        Finset.sum_le_sum fun j _ => hs j
    _ = 2 * Z ^ 2 * (∑ j, pderiv (fun y => ζ y * v y) j x ^ 2) + 2 * (Z ^ 2 * v x ^ 2) * ∑ j, pderiv ζ j x ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        have := (le_abs_self _).trans (by simpa using hM₂ x)
        have h4 : 2 * (Z ^ 2 * v x ^ 2) * ∑ j, pderiv ζ j x ^ 2 ≤ 2 * Z ^ 2 * M₂ * v x ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg Z) (sq_nonneg (v x))]
        linarith

/-- **E2** the uniform `H¹` bound for `ζ · (ρ ⋆ u)` (constant independent of `ρ`). -/
theorem energy_est (hb : ∀ i j, Sm (b i j)) (hsym : ∀ i j x, b i j x = b j i x) {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ Metric.closedBall (0 : Fin d → ℝ) R₀, ∀ ξ : Fin d → ℝ,
      lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, b i j x * ξ i * ξ j) (hC₁ : 0 ≤ C₁)
    (hζ : Sm ζ) (hζ0 : ∀ y, R₀ < ‖y‖ → ζ y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ u F : (Fin d → ℝ) → ℝ, FrKer ρ C₁ → (∀ x, ρ (-x) = ρ x) → MemLp u 2 volume →
      MemLp F 2 volume →
      (∀ a : (Fin d → ℝ) → ℝ, Sm a → (∀ y, R₀ + 1 < ‖y‖ → a y = 0) → ∫ x, u x * Pop b a x = ∫ x, F x * a x) →
      ∫ x, ∑ j, pderiv (fun y => ζ y * moll ρ u y) j x ^ 2 ≤ C * ((∫ x, u x ^ 2) + ∫ x, F x ^ 2) := by
  obtain ⟨CT, hCT0, hCT⟩ := comm_bound hb R₀ C₁ hC₁
  have hcsR : ∀ {f : (Fin d → ℝ) → ℝ}, (∀ y, R₀ < ‖y‖ → f y = 0) → HasCompactSupport f := fun {f} h =>
    hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R₀) fun y hy => h y (by simpa using hy)
  -- constants
  obtain ⟨Z, hZ⟩ := hζ.continuous.bounded_above_of_compact_support (hcsR hζ0)
  have hQc : Continuous (fun x => ∑ i, ∑ j, b i j x * pderiv ζ i x * pderiv ζ j x) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((hb i j).continuous.mul (hζ.pderiv i).continuous).mul (hζ.pderiv j).continuous)
  obtain ⟨M₁, hM₁⟩ := hQc.bounded_above_of_compact_support (hcsR fun y hy =>
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by simp [pderiv_zero_off hζ0 _ y hy])
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hRc : Continuous (fun x => ∑ j, pderiv ζ j x ^ 2) :=
    continuous_finsetSum _ fun j _ => (hζ.pderiv j).continuous.pow 2
  obtain ⟨M₂, hM₂⟩ := hRc.bounded_above_of_compact_support (hcsR fun y hy =>
    Finset.sum_eq_zero fun j _ => by simp [pderiv_zero_off hζ0 _ y hy])
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  refine ⟨2 * (M₁ + 1 / 2 + Z ^ 4 / 2 + (2 * CT * Z ^ 2 / lam + 1) / 2 + CT * Z ^ 2 * M₂ / (2 * CT * Z ^ 2 / lam + 1)) / lam,
    ?_, fun ρ u F hk heven hu hF veq => ?_⟩
  · have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
    positivity
  have hηpos : 0 < 2 * CT * Z ^ 2 / lam + 1 := by
    have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
    positivity
  have hu' : LocallyIntegrable u := hu.locallyIntegrable (by norm_num)
  have hF' : LocallyIntegrable F := hF.locallyIntegrable (by norm_num)
  have eid := energy_identity hb hsym hk heven hu' hF' veq hζ hζ0
  set v := moll ρ u with hv
  set V := moll ρ F with hV
  have hvS : Sm v := moll_contDiff hk.sm hk.cs hu'
  have hVS : Sm V := moll_contDiff hk.sm hk.cs hF'
  obtain ⟨hvi, hvJ⟩ := integral_sq_moll_le hk hu
  obtain ⟨hVi, hVJ⟩ := integral_sq_moll_le hk hF
  have hui : Integrable (fun x => u x ^ 2) := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 hu
  set w : (Fin d → ℝ) → ℝ := fun y => ζ y * v y with hw
  have hwS : Sm w := hζ.mul hvS
  set φ : (Fin d → ℝ) → ℝ := fun y => ζ y * (ζ y * v y) with hφ
  have hφS : Sm φ := hζ.mul hwS
  have hφ0 : ∀ y, R₀ < ‖y‖ → φ y = 0 := fun y hy => by simp [hφ, hζ0 y hy]
  have hw0 : ∀ y, R₀ < ‖y‖ → w y = 0 := fun y hy => by simp [hw, hζ0 y hy]
  have hdw0 : ∀ j y, R₀ < ‖y‖ → pderiv w j y = 0 := fun j y hy => pderiv_zero_off hw0 j y hy
  have hdφ0 : ∀ j y, R₀ < ‖y‖ → pderiv φ j y = 0 := fun j y hy => pderiv_zero_off hφ0 j y hy
  -- integrability of the pieces
  have iW : Integrable (fun x => ∑ j, pderiv w j x ^ 2) :=
    int_of_zero_off (R := R₀) (continuous_finsetSum _ fun j _ => (hwS.pderiv j).continuous.pow 2)
      fun y hy => Finset.sum_eq_zero fun j _ => by simp [hdw0 j y hy]
  have iE : Integrable (fun x => ∑ i, ∑ j, b i j x * pderiv w i x * pderiv w j x) :=
    int_of_zero_off (R := R₀) (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (((hb i j).continuous.mul (hwS.pderiv i).continuous).mul (hwS.pderiv j).continuous))
      fun y hy => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by simp [hdw0 j y hy]
  have iΦ : Integrable (fun x => ∑ j, pderiv φ j x ^ 2) :=
    int_of_zero_off (R := R₀) (continuous_finsetSum _ fun j _ => (hφS.pderiv j).continuous.pow 2)
      fun y hy => Finset.sum_eq_zero fun j _ => by simp [hdφ0 j y hy]
  have iA : Integrable (fun x => v x ^ 2 * ∑ i, ∑ j, b i j x * pderiv ζ i x * pderiv ζ j x) :=
    int_of_zero_off (R := R₀) ((hvS.continuous.pow 2).mul hQc) fun y hy => by
      simp [pderiv_zero_off hζ0 _ y hy]
  -- (a) ellipticity
  have hEll : lam * ∫ x, ∑ j, pderiv w j x ^ 2 ≤ ∫ x, ∑ i, ∑ j, b i j x * pderiv w i x * pderiv w j x := by
    rw [← integral_const_mul]
    refine integral_mono (iW.const_mul _) iE fun x => ?_
    by_cases hx : ‖x‖ ≤ R₀
    · exact hell x (by simpa using hx) (fun i => pderiv w i x)
    · have hx' : R₀ < ‖x‖ := not_le.1 hx
      simp [hdw0 _ x hx']
  -- (c) the `ζ'`-term
  have hA : ∫ x, v x ^ 2 * ∑ i, ∑ j, b i j x * pderiv ζ i x * pderiv ζ j x ≤ M₁ * ∫ x, v x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono iA (hvi.const_mul _) fun x => ?_
    have := (le_abs_self _).trans (by simpa using hM₁ x)
    nlinarith [sq_nonneg (v x)]
  -- (d) the right-hand side term
  have hq : Continuous (fun x => ζ x * (ζ x * v x)) := hφS.continuous
  have hqi : Integrable (fun x => (ζ x * (ζ x * v x)) ^ 2) :=
    int_of_zero_off (R := R₀) (hq.pow 2) fun y hy => by simp [hζ0 y hy]
  obtain ⟨hpq, hB⟩ := amgm_int (p := V) (q := fun x => ζ x * (ζ x * v x)) hVS.continuous.aestronglyMeasurable
    hq.aestronglyMeasurable hVi hqi (η := 1) one_pos
  have hqJ : ∫ x, (ζ x * (ζ x * v x)) ^ 2 ≤ Z ^ 4 * ∫ x, v x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono hqi (hvi.const_mul _) fun x => ?_
    have h1 : ζ x ^ 2 ≤ Z ^ 2 := sq_le_of_norm_le (hZ x)
    have h2 : (ζ x * (ζ x * v x)) ^ 2 = (ζ x ^ 2) ^ 2 * v x ^ 2 := by ring
    rw [h2]
    have h3 : (ζ x ^ 2) ^ 2 ≤ (Z ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    have : Z ^ 4 = (Z ^ 2) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  have hB' : |∫ x, V x * (ζ x * (ζ x * v x))| ≤ 1 / 2 * (∫ x, V x ^ 2) + 1 / 2 * (Z ^ 4 * ∫ x, v x ^ 2) := by
    have h5 : (2 : ℝ)⁻¹ * ∫ x, (ζ x * (ζ x * v x)) ^ 2 ≤ 2⁻¹ * (Z ^ 4 * ∫ x, v x ^ 2) :=
      mul_le_mul_of_nonneg_left hqJ (by norm_num)
    have := hB
    simp only [mul_one, one_div] at this ⊢
    linarith
  -- (e) the commutator term
  obtain ⟨hTi, hTle⟩ := hCT ρ φ hk hφS (tsupport_sub_of_zero_off hφ0)
  have hTc : Continuous (Tcomm b ρ φ) := (sm_Tcomm hb hk.sm hk.cs hφS).continuous
  obtain ⟨hpT, hC⟩ := amgm_int (p := u) (q := Tcomm b ρ φ) hu.aestronglyMeasurable hTc.aestronglyMeasurable hui hTi
    hηpos
  -- (f) bound `∫ Σ (∂φ)²`
  have hΦ : ∫ x, ∑ j, pderiv φ j x ^ 2 ≤ 2 * Z ^ 2 * (∫ x, ∑ j, pderiv w j x ^ 2) + 2 * Z ^ 2 * M₂ * ∫ x, v x ^ 2 := by
    have iR : Integrable (fun x => 2 * Z ^ 2 * (∑ j, pderiv w j x ^ 2) + 2 * Z ^ 2 * M₂ * v x ^ 2) :=
      (iW.const_mul _).add (hvi.const_mul _)
    calc ∫ x, ∑ j, pderiv φ j x ^ 2 ≤ ∫ x, (2 * Z ^ 2 * (∑ j, pderiv w j x ^ 2) + 2 * Z ^ 2 * M₂ * v x ^ 2) :=
          integral_mono iΦ iR fun x => phi_pointwise hζ hvS hZ hM₂ x
      _ = _ := by rw [integral_add (iW.const_mul _) (hvi.const_mul _), integral_const_mul, integral_const_mul]
  exact absorb hlam hCT0 hM₁0 hM₂0 rfl (integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _) hEll eid hA hB' hC hTle hΦ hvJ hVJ

end

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
