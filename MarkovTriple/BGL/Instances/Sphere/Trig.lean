import Mathlib

/-!
# Chebyshev polynomials of the second kind in the angle variable (S³ zonal eigenfunctions)

`Utheta k θ = ∑_{j ≤ k} cos((k-2j)θ) = sin((k+1)θ)/sin θ`.
-/

open Real

namespace MarkovTriple.BGL.Instances.Sphere

/-- `U_k(cos θ) = ∑_{j=0}^k cos((k-2j)θ)`. -/
noncomputable def Utheta (k : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), Real.cos (((k : ℝ) - 2 * j) * θ)

lemma Utheta_neg (k : ℕ) (θ : ℝ) : Utheta k (-θ) = Utheta k θ := by
  unfold Utheta
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_neg, Real.cos_neg]

lemma Utheta_add_two_pi (k : ℕ) (θ : ℝ) : Utheta k (θ + 2 * π) = Utheta k θ := by
  unfold Utheta
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ((k : ℝ) - 2 * j) * (θ + 2 * π) = ((k : ℝ) - 2 * j) * θ + ((k - 2 * j : ℤ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [this, Real.cos_add_int_mul_two_pi]

lemma contDiff_Utheta (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Utheta k) := by
  unfold Utheta
  refine ContDiff.sum fun j _ => ?_
  exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

lemma continuous_Utheta (k : ℕ) : Continuous (Utheta k) :=
  (contDiff_Utheta k).continuous

lemma Utheta_zero (k : ℕ) : Utheta k 0 = k + 1 := by
  simp [Utheta]

lemma sin_mul_Utheta (k : ℕ) (θ : ℝ) :
    Real.sin θ * Utheta k θ = Real.sin (((k : ℝ) + 1) * θ) := by
  unfold Utheta
  rw [Finset.mul_sum]
  set f : ℕ → ℝ := fun i => Real.sin (((k : ℝ) + 1 - 2 * i) * θ) with hf
  have h : ∀ j ∈ Finset.range (k + 1),
      Real.sin θ * Real.cos (((k : ℝ) - 2 * j) * θ) = (f j - f (j + 1)) / 2 := by
    intro j _
    simp only [hf]
    have e1 : ((k : ℝ) + 1 - 2 * j) * θ = ((k : ℝ) - 2 * j) * θ + θ := by ring
    have e2 : ((k : ℝ) + 1 - 2 * ((j + 1 : ℕ) : ℝ)) * θ = ((k : ℝ) - 2 * j) * θ - θ := by
      push_cast; ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_div, Finset.sum_range_sub']
  simp only [hf]
  have e3 : ((k : ℝ) + 1 - 2 * ((k + 1 : ℕ) : ℝ)) * θ = -(((k : ℝ) + 1) * θ) := by
    push_cast; ring
  rw [e3, Real.sin_neg]
  simp

lemma eq_of_sin_mul_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ θ, Real.sin θ * f θ = Real.sin θ * g θ) : f = g := by
  have hc : {θ : ℝ | Real.sin θ = 0}.Countable := by
    have : {θ : ℝ | Real.sin θ = 0} = Set.range (fun n : ℤ => (n : ℝ) * π) := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_range]
      rw [Real.sin_eq_zero_iff]
    rw [this]; exact Set.countable_range _
  have hd : Dense {θ : ℝ | Real.sin θ = 0}ᶜ := hc.dense_compl ℝ
  exact Continuous.ext_on hd hf hg (fun x hx =>
    mul_left_cancel₀ (show Real.sin x ≠ 0 from hx) (h x))

lemma two_cos_mul_sin (a θ : ℝ) :
    2 * Real.cos θ * Real.sin a = Real.sin (a + θ) + Real.sin (a - θ) := by
  rw [Real.sin_add, Real.sin_sub]; ring

lemma recurrence_zero (θ : ℝ) : 2 * Real.cos θ * Utheta 0 θ = Utheta 1 θ := by
  have := congrFun (eq_of_sin_mul_eq (f := fun θ => 2 * Real.cos θ * Utheta 0 θ)
    (g := Utheta 1) (by have := continuous_Utheta 0; fun_prop) (continuous_Utheta 1)
    (fun θ => by
      have h0 := sin_mul_Utheta 0 θ
      have h1 := sin_mul_Utheta 1 θ
      have h2 := two_cos_mul_sin θ θ
      push_cast at h0 h1
      simp only [zero_add, one_mul] at h0
      have e : (1 + 1 : ℝ) * θ = θ + θ := by ring
      rw [e] at h1
      simp only [sub_self, Real.sin_zero, add_zero] at h2
      calc Real.sin θ * (2 * Real.cos θ * Utheta 0 θ)
          = 2 * Real.cos θ * (Real.sin θ * Utheta 0 θ) := by ring
        _ = _ := by rw [h0, h2, h1])) θ
  exact this

lemma recurrence_succ (k : ℕ) (θ : ℝ) :
    2 * Real.cos θ * Utheta (k + 1) θ = Utheta (k + 2) θ + Utheta k θ := by
  have := congrFun (eq_of_sin_mul_eq (f := fun θ => 2 * Real.cos θ * Utheta (k + 1) θ)
    (g := fun θ => Utheta (k + 2) θ + Utheta k θ)
    (by have := continuous_Utheta (k + 1); fun_prop)
    ((continuous_Utheta _).add (continuous_Utheta _))
    (fun θ => by
      have h0 := sin_mul_Utheta k θ
      have h1 := sin_mul_Utheta (k + 1) θ
      have h2 := sin_mul_Utheta (k + 2) θ
      have h3 := two_cos_mul_sin (((k : ℝ) + 2) * θ) θ
      push_cast at h1 h2
      have e1 : ((k : ℝ) + 2) * θ + θ = ((k : ℝ) + 1 + 1 + 1) * θ := by ring
      have e2 : ((k : ℝ) + 2) * θ - θ = ((k : ℝ) + 1) * θ := by ring
      have e3 : ((k : ℝ) + 1 + 1) * θ = ((k : ℝ) + 2) * θ := by ring
      rw [e1, e2] at h3
      rw [e3] at h1
      calc Real.sin θ * (2 * Real.cos θ * Utheta (k + 1) θ)
          = 2 * Real.cos θ * (Real.sin θ * Utheta (k + 1) θ) := by ring
        _ = Real.sin θ * (Utheta (k + 2) θ + Utheta k θ) := by
          rw [h1, h3, mul_add, h2, h0]; ring_nf)) θ
  exact this

/-! ### Derivatives -/

/-- the `m`-th derivative of `Utheta k`, explicitly. -/
noncomputable def UD (m k : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ((k : ℝ) - 2 * j) ^ m *
    Real.cos (((k : ℝ) - 2 * j) * θ + m * (π / 2))

lemma hasDerivAt_UD (m k : ℕ) (θ : ℝ) : HasDerivAt (UD m k) (UD (m + 1) k θ) θ := by
  unfold UD
  have := HasDerivAt.fun_sum (u := Finset.range (k + 1))
    (A := fun j => fun θ => ((k : ℝ) - 2 * j) ^ m *
      Real.cos (((k : ℝ) - 2 * j) * θ + m * (π / 2)))
    (A' := fun j => ((k : ℝ) - 2 * j) ^ (m + 1) *
      Real.cos (((k : ℝ) - 2 * j) * θ + ((m + 1 : ℕ) : ℝ) * (π / 2))) (x := θ)
    (fun j _ => by
      have h1 : HasDerivAt (fun θ : ℝ => ((k : ℝ) - 2 * j) * θ + m * (π / 2))
          ((k : ℝ) - 2 * j) θ := by
        simpa using ((hasDerivAt_id θ).const_mul ((k : ℝ) - 2 * j)).add_const ((m : ℝ) * (π / 2))
      have h2 := (h1.cos).const_mul (((k : ℝ) - 2 * j) ^ m)
      convert h2 using 1
      have : Real.cos (((k : ℝ) - 2 * j) * θ + ((m + 1 : ℕ) : ℝ) * (π / 2)) =
          -Real.sin (((k : ℝ) - 2 * j) * θ + m * (π / 2)) := by
        have e : ((k : ℝ) - 2 * j) * θ + ((m + 1 : ℕ) : ℝ) * (π / 2) =
            (((k : ℝ) - 2 * j) * θ + m * (π / 2)) + π / 2 := by push_cast; ring
        rw [e, Real.cos_add_pi_div_two]
      rw [this]; ring)
  convert this using 1

lemma UD_zero (k : ℕ) : UD 0 k = Utheta k := by
  funext θ; simp [UD, Utheta]

lemma iteratedDeriv_Utheta (m k : ℕ) : iteratedDeriv m (Utheta k) = UD m k := by
  induction m with
  | zero => rw [iteratedDeriv_zero, UD_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    exact (hasDerivAt_UD m k θ).deriv

lemma deriv_Utheta (k : ℕ) : deriv (Utheta k) = UD 1 k := by
  have := iteratedDeriv_Utheta 1 k
  rwa [iteratedDeriv_one] at this

lemma deriv_deriv_Utheta (k : ℕ) : deriv (deriv (Utheta k)) = UD 2 k := by
  have := iteratedDeriv_Utheta 2 k
  rwa [iteratedDeriv_succ, iteratedDeriv_one] at this

lemma abs_UD_le (m k : ℕ) (θ : ℝ) : |UD m k θ| ≤ (k + 1) * (k : ℝ) ^ m := by
  unfold UD
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ j ∈ Finset.range (k + 1),
      |((k : ℝ) - 2 * j) ^ m * Real.cos (((k : ℝ) - 2 * j) * θ + m * (π / 2))| ≤ (k : ℝ) ^ m := by
    intro j hj
    have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj'
    have ha : |(k : ℝ) - 2 * j| ≤ k := by
      rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    rw [abs_mul, abs_pow]
    calc |(k : ℝ) - 2 * j| ^ m * |Real.cos _| ≤ (k : ℝ) ^ m * 1 :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha m) (Real.abs_cos_le_one _)
            (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma abs_iteratedDeriv_Utheta_le (m k : ℕ) (θ : ℝ) :
    |iteratedDeriv m (Utheta k) θ| ≤ (k + 1) * (k : ℝ) ^ m := by
  rw [iteratedDeriv_Utheta]; exact abs_UD_le m k θ

lemma norm_iteratedFDeriv_Utheta_le (m k : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ m (Utheta k) θ‖ ≤ (k + 1) * (k : ℝ) ^ m := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact abs_iteratedDeriv_Utheta_le m k θ

/-! ### Eigen equation -/

lemma Utheta_eigen_aux (k : ℕ) (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    deriv (deriv (Utheta k)) θ + 2 * (Real.cos θ * (deriv (Utheta k) θ / Real.sin θ)) =
      -((k : ℝ) * (k + 2)) * Utheta k θ := by
  rw [deriv_deriv_Utheta, deriv_Utheta]
  have hU : ∀ θ, HasDerivAt (Utheta k) (UD 1 k θ) θ := fun θ => by
    have := hasDerivAt_UD 0 k θ
    rwa [UD_zero] at this
  -- first identity
  have A : ∀ θ, Real.cos θ * Utheta k θ + Real.sin θ * UD 1 k θ =
      ((k : ℝ) + 1) * Real.cos (((k : ℝ) + 1) * θ) := by
    intro θ
    have h1 : HasDerivAt (fun θ => Real.sin θ * Utheta k θ)
        (Real.cos θ * Utheta k θ + Real.sin θ * UD 1 k θ) θ :=
      (Real.hasDerivAt_sin θ).mul (hU θ)
    have h2 : HasDerivAt (fun θ => Real.sin (((k : ℝ) + 1) * θ))
        (Real.cos (((k : ℝ) + 1) * θ) * ((k : ℝ) + 1)) θ := by
      have := ((hasDerivAt_id θ).const_mul ((k : ℝ) + 1)).sin
      simpa using this
    have e : (fun θ => Real.sin θ * Utheta k θ) = fun θ => Real.sin (((k : ℝ) + 1) * θ) :=
      funext (sin_mul_Utheta k)
    rw [e] at h1
    rw [h1.unique h2]; ring
  have hU1 : ∀ θ, HasDerivAt (UD 1 k) (UD 2 k θ) θ := fun θ => hasDerivAt_UD 1 k θ
  have h3 : HasDerivAt (fun θ => Real.cos θ * Utheta k θ + Real.sin θ * UD 1 k θ)
      (-Real.sin θ * Utheta k θ + Real.cos θ * UD 1 k θ + (Real.cos θ * UD 1 k θ +
        Real.sin θ * UD 2 k θ)) θ :=
    ((Real.hasDerivAt_cos θ).mul (hU θ)).add ((Real.hasDerivAt_sin θ).mul (hU1 θ))
  have h4 : HasDerivAt (fun θ => ((k : ℝ) + 1) * Real.cos (((k : ℝ) + 1) * θ))
      (((k : ℝ) + 1) * (-Real.sin (((k : ℝ) + 1) * θ) * ((k : ℝ) + 1))) θ := by
    have := (((hasDerivAt_id θ).const_mul ((k : ℝ) + 1)).cos).const_mul ((k : ℝ) + 1)
    simpa using this
  have e : (fun θ => Real.cos θ * Utheta k θ + Real.sin θ * UD 1 k θ) =
      fun θ => ((k : ℝ) + 1) * Real.cos (((k : ℝ) + 1) * θ) := funext A
  rw [e] at h3
  have B := h3.unique h4
  have hs := sin_mul_Utheta k θ
  field_simp
  linear_combination B + ((k : ℝ) + 1) ^ 2 * hs

/-! ### Orthonormality -/

lemma integral_cos_mul_pi (c : ℤ) :
    ∫ θ in (0:ℝ)..π, Real.cos ((c : ℝ) * θ) = if c = 0 then π else 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    rw [ite_eq_right hc, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc']
    simp [Real.sin_int_mul_pi]

lemma integral_sin_mul_sin (a b : ℕ) :
    ∫ θ in (0:ℝ)..π, Real.sin (((a : ℝ) + 1) * θ) * Real.sin (((b : ℝ) + 1) * θ) =
      if a = b then π / 2 else 0 := by
  have e : ∀ θ : ℝ, Real.sin (((a : ℝ) + 1) * θ) * Real.sin (((b : ℝ) + 1) * θ) =
      (Real.cos ((((a : ℤ) - b : ℤ) : ℝ) * θ) - Real.cos ((((a : ℤ) + b + 2 : ℤ) : ℝ) * θ)) / 2 := by
    intro θ
    push_cast
    have h1 : ((a : ℝ) - b) * θ = ((a : ℝ) + 1) * θ - ((b : ℝ) + 1) * θ := by ring
    have h2 : ((a : ℝ) + b + 2) * θ = ((a : ℝ) + 1) * θ + ((b : ℝ) + 1) * θ := by ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun θ : ℝ => Real.cos ((((a : ℤ) - b : ℤ) : ℝ) * θ)) MeasureTheory.volume 0 π :=
    (by fun_prop : Continuous fun θ : ℝ => Real.cos ((((a : ℤ) - b : ℤ) : ℝ) * θ)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => Real.cos ((((a : ℤ) + b + 2 : ℤ) : ℝ) * θ)) MeasureTheory.volume 0 π :=
    (by fun_prop : Continuous fun θ : ℝ => Real.cos ((((a : ℤ) + b + 2 : ℤ) : ℝ) * θ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub i1 i2,
    integral_cos_mul_pi, integral_cos_mul_pi]
  have h0 : ((a : ℤ) + b + 2) ≠ 0 := by omega
  rw [ite_eq_right h0]
  by_cases hab : a = b
  · subst hab; simp
  · have : ((a : ℤ) - b) ≠ 0 := by omega
    simp [hab, this]

lemma integral_Utheta_mul (j k : ℕ) :
    ∫ θ in (0:ℝ)..π, (2 / π) * Real.sin θ ^ 2 * (Utheta j θ * Utheta k θ) =
      if j = k then 1 else 0 := by
  have e : ∀ θ : ℝ, (2 / π) * Real.sin θ ^ 2 * (Utheta j θ * Utheta k θ) =
      (2 / π) * (Real.sin (((j : ℝ) + 1) * θ) * Real.sin (((k : ℝ) + 1) * θ)) := by
    intro θ
    rw [← sin_mul_Utheta j, ← sin_mul_Utheta k]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_sin_mul_sin]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  by_cases h : j = k
  · simp [h]
  · simp [h]

end MarkovTriple.BGL.Instances.Sphere
