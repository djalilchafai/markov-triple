import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Full.F8

/-!
# Orthogonality of the spherical-harmonic eigenspaces and coefficient decay (Round 31, stream V, steps 2-3)

BGL §2.2 / C.5.  From the symmetry of `L_S` (`ibp_sphere`): restrictions of harmonic homogeneous polynomials of
different degrees are `L²(σ)`-orthogonal, and the pairing `∫ f h` of `f ∈ 𝒜₀` with a degree-`k` harmonic `h`
satisfies `λ_k^m ∫ f h = (-1)^m ∫ (L^m f) h`.
-/

open MeasureTheory

namespace MarkovTriple.BGL.SphereN

variable {n : ℕ}

/-- symmetry of `L_S` on `𝒜₀S`. -/
theorem LS_symm (hn : 1 ≤ n) {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) :
    ∫ x, g x * LS f x ∂σ n = ∫ x, f x * LS g x ∂σ n := by
  have h1 := ibp_sphere hn hf hg
  have h2 := ibp_sphere hn hg hf
  rw [ΓS_symm g f] at h2
  linarith

lemma lamS_strictMono (hn : 2 ≤ n) {k k' : ℕ} (h : k < k') : lamS n k < lamS n k' := by
  unfold lamS
  have hk : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- **Orthogonality of eigenspaces**: harmonic homogeneous polynomials of different degrees are orthogonal in
`L²(σ)`. -/
theorem harm_orth (hn : 2 ≤ n) {k k' : ℕ} {h h' : Pn n} (hh : IsHarm k h) (hh' : IsHarm k' h')
    (hk : k ≠ k') : ∫ x, restr h x * restr h' x ∂σ n = 0 := by
  have hs := LS_symm (n := n) (by omega) (restr_mem h) (restr_mem h')
  rw [LS_restr_harm hh, LS_restr_harm hh'] at hs
  have e : (-(lamS n k')) * ∫ x, restr h x * restr h' x ∂σ n
      = (-(lamS n k)) * ∫ x, restr h x * restr h' x ∂σ n := by
    have a : ∫ x, restr h' x * (-((k : ℝ) * (k + n - 2)) * restr h x) ∂σ n
        = (-(lamS n k)) * ∫ x, restr h x * restr h' x ∂σ n := by
      rw [← integral_const_mul]; congr 1; funext x; unfold lamS; ring
    have b : ∫ x, restr h x * (-((k' : ℝ) * (k' + n - 2)) * restr h' x) ∂σ n
        = (-(lamS n k')) * ∫ x, restr h x * restr h' x ∂σ n := by
      rw [← integral_const_mul]; congr 1; funext x; unfold lamS; ring
    rw [a, b] at hs
    exact hs.symm
  rcases lt_or_gt_of_ne hk with c | c
  · have := lamS_strictMono hn c
    have h2 : (lamS n k' - lamS n k) * ∫ x, restr h x * restr h' x ∂σ n = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · exact h3
  · have := lamS_strictMono hn c
    have h2 : (lamS n k - lamS n k') * ∫ x, restr h x * restr h' x ∂σ n = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · exact h3

/-- one step of coefficient decay: `λ_k ∫ f h = -∫ (L f) h`. -/
theorem coeff_step (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) {f : Sph n → ℝ} (hf : f ∈ A₀S n) :
    lamS n k * ∫ x, f x * restr h x ∂σ n = -∫ x, LS f x * restr h x ∂σ n := by
  have hs := LS_symm (n := n) (by omega) hf (restr_mem h)
  rw [LS_restr_harm hh] at hs
  have a : ∫ x, f x * (-((k : ℝ) * (k + n - 2)) * restr h x) ∂σ n
      = -(lamS n k * ∫ x, f x * restr h x ∂σ n) := by
    rw [← integral_const_mul, ← integral_neg]; congr 1; funext x; unfold lamS; ring
  have b : ∫ x, restr h x * LS f x ∂σ n = ∫ x, LS f x * restr h x ∂σ n := by
    congr 1; funext x; ring
  rw [a, b] at hs
  linarith

/-- iterated coefficient decay: `λ_k^m ∫ f h = (-1)^m ∫ (L^m f) h`, with `L^m f ∈ 𝒜₀S`. -/
theorem coeff_pow (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) (m : ℕ) {f : Sph n → ℝ}
    (hf : f ∈ A₀S n) :
    (LS)^[m] f ∈ A₀S n ∧
      lamS n k ^ m * ∫ x, f x * restr h x ∂σ n
        = (-1) ^ m * ∫ x, ((LS)^[m] f) x * restr h x ∂σ n := by
  induction m generalizing f with
  | zero => simp [hf]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih (LS_mem hf)
    refine ⟨by rw [Function.iterate_succ_apply]; exact h1, ?_⟩
    rw [Function.iterate_succ_apply, pow_succ, pow_succ, mul_assoc, coeff_step hn hh hf]
    have : lamS n k ^ m * -∫ x, LS f x * restr h x ∂σ n
        = -(lamS n k ^ m * ∫ x, LS f x * restr h x ∂σ n) := by ring
    rw [this, h2]; ring

end MarkovTriple.BGL.SphereN
