import MarkovTriple.Sanity.OU.Density

/-! # OU (Part 6): the Hermite Hilbert basis of `L²(γ)` -/

open MeasureTheory Filter Topology ProbabilityTheory Polynomial
open scoped ENNReal NNReal Real InnerProductSpace

namespace MarkovTriple.Sanity.OU

lemma inner_toLp {f g : ℝ → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂γ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]; simp [mul_comm]

/-- the Hermite basis vectors in `L²(γ)` -/
noncomputable def hL (n : ℕ) : Lp ℝ 2 γ := (hh_memLp n).toLp (hh n)

lemma orthonormal_hL : Orthonormal ℝ hL := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [hL, hL, inner_toLp, integral_hh_hh]

lemma inner_hL (n : ℕ) (w : Lp ℝ 2 γ) : ⟪hL n, w⟫_ℝ = ∫ x, hh n x * w x ∂γ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(hh_memLp n).coeFn_toLp] with x h1
  rw [hL, h1]; simp [mul_comm]

lemma poly_mem_span_He (p : ℝ[X]) : p ∈ Submodule.span ℝ (Set.range He) := by
  suffices H : ∀ d : ℕ, ∀ p : ℝ[X], p.natDegree ≤ d → p ∈ Submodule.span ℝ (Set.range He) from
    H _ p le_rfl
  intro d
  induction d with
  | zero =>
    intro p hp
    rw [Polynomial.eq_C_of_natDegree_le_zero hp]
    have : (C (p.coeff 0) : ℝ[X]) = p.coeff 0 • He 0 := by
      rw [He_zero, smul_eq_C_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | succ d ih =>
    intro p hp
    set c := p.coeff (d + 1)
    have hq : (p - c • He (d + 1)).natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      have hk' : d + 1 ≤ k := hk
      rw [coeff_sub, coeff_smul]
      rcases Nat.eq_or_lt_of_le hk' with h | h
      · subst h; simp [c, He_coeff_self]
      · have h1 : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have h2 : (He (d + 1)).coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [He_natDegree]; omega)
        simp [h1, h2]
    have := ih _ hq
    have e : p = (p - c • He (d + 1)) + c • He (d + 1) := by ring
    rw [e]
    exact Submodule.add_mem _ this
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨d + 1, rfl⟩))

lemma eq_zero_of_orth_hL {w : Lp ℝ 2 γ} (h : ∀ n, ⟪hL n, w⟫_ℝ = 0) : w = 0 := by
  have hw := Lp.memLp w
  have key : ∀ p ∈ Submodule.span ℝ (Set.range He), ∫ x, p.eval x * w x ∂γ = 0 := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨n, rfl⟩ := hq
      have := h n
      rw [inner_hL] at this
      have e : ∀ x, hh n x * w x = (√(n.factorial : ℝ))⁻¹ * ((He n).eval x * w x) := by
        intro x; simp only [hh]; ring
      simp_rw [e] at this
      rw [integral_const_mul] at this
      have hne : (√(n.factorial : ℝ))⁻¹ ≠ 0 := by
        have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
        exact inv_ne_zero (Real.sqrt_pos.2 this).ne'
      exact (mul_eq_zero.1 this).resolve_left hne
    | zero => simp
    | add p q _ _ hp hq =>
      have i1 : Integrable (fun x => p.eval x * w x) γ := (pf_PG p).memLp_two.integrable_mul hw
      have i2 : Integrable (fun x => q.eval x * w x) γ := (pf_PG q).memLp_two.integrable_mul hw
      simp only [eval_add, add_mul]
      rw [integral_add i1 i2, hp, hq, add_zero]
    | smul c p _ hp =>
      simp only [eval_smul, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, hp, mul_zero]
  have hz : (w : ℝ → ℝ) =ᵐ[γ] 0 := by
    refine eq_zero_of_orth_poly _ hw fun n => ?_
    have := key (X ^ n) (poly_mem_span_He _)
    simpa using this
  exact Lp.eq_zero_iff_ae_eq_zero.2 hz

end MarkovTriple.Sanity.OU
