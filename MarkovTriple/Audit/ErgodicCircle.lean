import Mathlib
import MarkovTriple.Audit.ErgodicA
import MarkovTriple.Sanity.Circle

open MeasureTheory Filter AddCircle
open scoped Topology ENNReal Real

namespace MarkovTriple.Sanity.Circle

noncomputable def ek (k : ℕ) : 𝕋 → ℝ := fun x => (fourier (k : ℤ) x).re
noncomputable def sk (k : ℕ) : 𝕋 → ℝ := fun x => (fourier (k : ℤ) x).im

lemma cC_mem : (⇑cC : 𝕋 → ℝ) ∈ A₀ := Atrig_le (Algebra.subset_adjoin (by simp))
lemma sC_mem : (⇑sC : 𝕋 → ℝ) ∈ A₀ := Atrig_le (Algebra.subset_adjoin (by simp))

lemma ek_succ (k : ℕ) : ek (k + 1) = ek k * ⇑cC + (-1 : ℝ) • (sk k * ⇑sC) := by
  funext x
  have h : fourier ((k + 1 : ℕ) : ℤ) x = fourier (k : ℤ) x * fourier 1 x := by
    push_cast; exact fourier_add
  simp only [ek, sk, h, Complex.mul_re, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  change _ = _ * (fourier 1 x).re + (-1) * (_ * (fourier 1 x).im)
  ring

lemma sk_succ (k : ℕ) : sk (k + 1) = ek k * ⇑sC + sk k * ⇑cC := by
  funext x
  have h : fourier ((k + 1 : ℕ) : ℤ) x = fourier (k : ℤ) x * fourier 1 x := by
    push_cast; exact fourier_add
  simp only [ek, sk, h, Complex.mul_im, Pi.add_apply, Pi.mul_apply]
  change _ = _ * (fourier 1 x).im + _ * (fourier 1 x).re
  ring

lemma ek_sk (k : ℕ) : ek k ∈ A₀ ∧ sk k ∈ A₀ ∧ D (ek k) = (-(2 * π * k)) • sk k ∧
    D (sk k) = (2 * π * k) • ek k := by
  induction k with
  | zero =>
    have e0 : ek 0 = fun _ => (1 : ℝ) := by funext x; simp [ek]
    have s0 : sk 0 = fun _ => (0 : ℝ) := by funext x; simp [sk]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e0]; exact Atrig_le (Atrig.algebraMap_mem 1)
    · rw [s0]; exact Atrig_le (Atrig.algebraMap_mem 0)
    · rw [e0, s0, D_const]; simp
    · rw [e0, s0, D_const]; simp
  | succ k ih =>
    obtain ⟨he, hs, hDe, hDs⟩ := ih
    have hc := cC_mem; have hs' := sC_mem
    have m1 : ek k * ⇑cC ∈ A₀ := mul_mem he hc
    have m2 : sk k * ⇑sC ∈ A₀ := mul_mem hs hs'
    have m3 : ek k * ⇑sC ∈ A₀ := mul_mem he hs'
    have m4 : sk k * ⇑cC ∈ A₀ := mul_mem hs hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ek_succ]; exact add_mem m1 (A₀.smul_mem _ m2)
    · rw [sk_succ]; exact add_mem m3 m4
    · rw [ek_succ, D_add (Sm_of_mem m1) (Sm_of_mem (A₀.smul_mem _ m2)),
        D_smul _ (Sm_of_mem m2), D_mul' he hc, D_mul' hs hs', hDe, hDs, D_c, D_s]
      funext x
      simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [sk_succ]
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    · rw [sk_succ, D_add (Sm_of_mem m3) (Sm_of_mem m4),
        D_mul' he hs', D_mul' hs hc, hDe, hDs, D_c, D_s]
      funext x
      simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [ek_succ]
      simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring


lemma L_ek (k : ℕ) : Lc (ek k) = (-(2 * π * k) * (2 * π * k)) • ek k := by
  obtain ⟨he, hs, hDe, hDs⟩ := ek_sk k
  unfold Lc
  rw [hDe, D_smul _ (Sm_of_mem hs), hDs]
  funext x; simp; ring

lemma L_sk (k : ℕ) : Lc (sk k) = (-(2 * π * k) * (2 * π * k)) • sk k := by
  obtain ⟨he, hs, hDe, hDs⟩ := ek_sk k
  unfold Lc
  rw [hDs, D_smul _ (Sm_of_mem he), hDe]
  funext x; simp; ring

lemma ek_memLp (k : ℕ) : MemLp (ek k) 2 μ₀ := memLp_of_mem (ek_sk k).1 2
lemma sk_memLp (k : ℕ) : MemLp (sk k) 2 μ₀ := memLp_of_mem (ek_sk k).2.1 2

noncomputable abbrev fB : HilbertBasis ℤ ℂ (Lp ℂ 2 μ₀) := fourierBasis (T := 1)

/-- A real `L²` function on the circle orthogonal to all `cos 2πkx`, `sin 2πkx`, `k ≥ 1`, is
a.e. constant (completeness of the Fourier basis). -/
theorem const_of_orth (u : 𝕋 → ℝ) (hu : MemLp u 2 μ₀)
    (h1 : ∀ k : ℕ, 1 ≤ k → ∫ x, u x * ek k x ∂μ₀ = 0)
    (h2 : ∀ k : ℕ, 1 ≤ k → ∫ x, u x * sk k x ∂μ₀ = 0) :
    ∃ c : ℝ, u =ᵐ[μ₀] fun _ => c := by
  have hc : MemLp (fun x => (u x : ℂ)) 2 μ₀ := hu.ofReal
  set U : Lp ℂ 2 μ₀ := hc.toLp _ with hU
  have hUae : (U : 𝕋 → ℂ) =ᵐ[μ₀] fun x => (u x : ℂ) := MemLp.coeFn_toLp hc
  -- coefficients
  have coeff : ∀ n : ℤ, n ≠ 0 → fourierCoeff (fun x => (u x : ℂ)) n = 0 := by
    intro n hn
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ (n = m ∨ n = -m) := by
      refine ⟨n.natAbs, Int.natAbs_pos.2 hn, ?_⟩
      omega
    obtain ⟨hm1, hm2⟩ := hm
    have iu1 : Integrable (fun x => u x * ek m x) μ₀ := (hu.integrable_mul (ek_memLp m))
    have iu2 : Integrable (fun x => u x * sk m x) μ₀ := (hu.integrable_mul (sk_memLp m))
    unfold fourierCoeff
    have hre : ∀ x : 𝕋, (fourier (-n) x • (u x : ℂ)).re = u x * ek m x := by
      intro x
      rcases hm2 with rfl | rfl
      · rw [fourier_neg, smul_eq_mul]
        simp [ek]; ring
      · rw [neg_neg, smul_eq_mul]
        simp [ek]; ring
    have him : ∀ x : 𝕋, (fourier (-n) x • (u x : ℂ)).im = (if n = m then -1 else 1) * (u x * sk m x) := by
      intro x
      rcases hm2 with rfl | rfl
      · rw [fourier_neg, smul_eq_mul]
        simp [sk]; ring
      · rw [neg_neg, smul_eq_mul]
        have : ¬ ((-(m : ℤ)) = (m : ℤ)) := by omega
        simp [sk, this]; ring
    have iF : Integrable (fun x => fourier (-n) x • (u x : ℂ)) μ₀ := by
      refine Integrable.mono' ((hu.integrable (by norm_num)).norm) ?_ ?_
      · exact (((fourier (-n)).continuous.aestronglyMeasurable).smul
          hc.aestronglyMeasurable)
      · filter_upwards with x
        simp
    have eR := integral_re iF
    have eI := integral_im iF
    simp only [RCLike.re_to_complex, RCLike.im_to_complex] at eR eI
    apply Complex.ext
    · change (∫ x, fourier (-n) x • (u x : ℂ) ∂μ₀).re = 0
      rw [← eR]
      simp only [hre]
      simp [h1 m hm1]
    · change (∫ x, fourier (-n) x • (u x : ℂ) ∂μ₀).im = 0
      rw [← eI]
      simp only [him]
      rw [integral_const_mul, h2 m hm1]; simp
  set c : ℂ := fourierCoeff (fun x => (u x : ℂ)) 0 with hc0
  have hrepr : fB.repr U = fB.repr (c • fB (0 : ℤ)) := by
    ext n
    rw [map_smul, fourierBasis_repr, fB.repr_self]
    rw [fourierCoeff_congr_ae hUae]
    by_cases hn : n = 0
    · subst hn; simp [hc0]
    · simp [hn, coeff n hn]
  have hUc : U = c • fB (0 : ℤ) := fB.repr.injective hrepr
  have hb : (fB (0 : ℤ) : 𝕋 → ℂ) =ᵐ[μ₀] fun _ => 1 := by
    unfold fB; rw [coe_fourierBasis]
    filter_upwards [coeFn_fourierLp 2 (0 : ℤ)] with x hx
    rw [hx]; simp
  refine ⟨c.re, ?_⟩
  filter_upwards [hUae, hb, Lp.coeFn_smul c (fB (0 : ℤ))] with x h1 h2 h3
  have : (U : 𝕋 → ℂ) x = c := by
    rw [hUc, h3]; simp only [Pi.smul_apply, h2, smul_eq_mul, mul_one]
  rw [this] at h1
  have := congrArg Complex.re h1
  simpa using this.symm


/-- **The circle triple is ergodic in the `L²`-closure sense** (fully proved; nontrivial triple,
`Γ ≠ 0`). Hence `ErgodicL2` is satisfiable and not vacuous / not trivially false. -/
theorem circle_ErgodicL2 : circleTriple.ErgodicL2 := by
  intro u ⟨f, hf, h1, h2⟩
  have key : ∀ (g : 𝕋 → ℝ) (c : ℝ), g ∈ A₀ → c ≠ 0 → Lc g = c • g →
      ∫ x, (u : 𝕋 → ℝ) x * g x ∂μ₀ = 0 := by
    intro g c hg hc hL
    have := MarkovTriple.Audit.ker_orth circleTriple u f hf h1 h2 g hg
    have e : (circleTriple.L g) = c • g := hL
    rw [e] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have : ∫ x, c * ((u : 𝕋 → ℝ) x * g x) ∂μ₀ = 0 := by
      rw [← this]; congr 1; funext x; ring
    rw [integral_const_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  refine const_of_orth u (Lp.memLp u) (fun k hk => ?_) (fun k hk => ?_)
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    exact key (ek k) _ (ek_sk k).1 (by have := Real.pi_pos; nlinarith [mul_pos (mul_pos two_pos this) hk']) (L_ek k)
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    exact key (sk k) _ (ek_sk k).2.1 (by have := Real.pi_pos; nlinarith [mul_pos (mul_pos two_pos this) hk']) (L_sk k)

end MarkovTriple.Sanity.Circle

#print axioms MarkovTriple.Sanity.Circle.circle_ErgodicL2
