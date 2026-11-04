import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllRadial

/-!
# `RadialExh ⇒ CoreCut` (R19, Stream A6; target T6)

`coreCut_of_radial`: if `ψ` is a radial exhaustion (`RadialJets`), the cut-offs `χ_n = σ(ψ/(n+1))` form a `CutFamily`.
The proof is the scale-invariant bookkeeping `radial_scalar` (on the annulus `R ≤ ψ ≤ 2R`) plus the identities of
`radial_identities`.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

/-- scale-invariant scalar bound on the annulus. -/
lemma radial_scalar {M C R r s : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C) (hR : 1 ≤ R) (hrR : r * R = 1)
    {σ1 σ2 σ3 σ4 a a1 a2 b b1 b2 : ℝ} (hs1 : |σ1| ≤ M) (hs2 : |σ2| ≤ M) (hs3 : |σ3| ≤ M) (hs4 : |σ4| ≤ M)
    (hsR : R ≤ s) (hs2R : s ≤ 2 * R) (hg1 : |a| ≤ C * (1 + s)) (hg2 : 0 ≤ b) (hg3 : b ≤ C * (1 + s) ^ 2)
    (hg4 : |a1| ≤ C) (hg5 : |b1| ≤ C * (1 + s)) (hg6 : |a2| * (1 + s) ≤ C) (hg7 : |b2| ≤ C) :
    let f1 := r ^ 1 * σ1
    let f2 := r ^ 2 * σ2
    let f3 := r ^ 3 * σ3
    let f4 := r ^ 4 * σ4
    |f1 * f1 * b| ≤ 16 * (M + 9 * C) ^ 5 ∧ |f1 * a + f2 * b| ≤ 16 * (M + 9 * C) ^ 5 ∧
    |qP1' f1 f2 f3 a a1 b b1 * a + qP1'' f1 f2 f3 f4 a a1 a2 b b1 b2 * b| ≤ 16 * (M + 9 * C) ^ 5 ∧
    |qP1' f1 f2 f3 a a1 b b1 * qP1' f1 f2 f3 a a1 b b1 * b| ≤ 16 * (M + 9 * C) ^ 5 ∧
    |(qΘ' f1 f2 b b1 * a + qΘ'' f1 f2 f3 b b1 b2 * b - 2 * (qP1' f1 f2 f3 a a1 b b1 * f1 * b)) / 2| ≤
      16 * (M + 9 * C) ^ 5 := by
  intro f1 f2 f3 f4
  have hR0 : 0 < R := by linarith
  have hr0 : 0 < r := by
    by_contra h
    push Not at h
    nlinarith
  have hr1 : r ≤ 1 := by nlinarith
  have hB : 1 ≤ M + 9 * C := by linarith
  set B : ℝ := M + 9 * C with hBdef
  have hs0 : 0 ≤ s := by linarith
  have h1s : 0 < 1 + s := by linarith
  -- r (1 + s) ≤ 3
  have hrs : r * (1 + s) ≤ 3 := by
    have : r * (1 + s) = r + r * s := by ring
    have h2 : r * s ≤ 2 := by nlinarith
    linarith
  have hrs0 : 0 ≤ r * (1 + s) := by positivity
  have x1 : |r * a| ≤ B := by
    rw [abs_mul, abs_of_pos hr0]
    calc r * |a| ≤ r * (C * (1 + s)) := mul_le_mul_of_nonneg_left hg1 hr0.le
      _ = C * (r * (1 + s)) := by ring
      _ ≤ C * 3 := mul_le_mul_of_nonneg_left hrs hC
      _ ≤ B := by rw [hBdef]; linarith
  have x2 : |r ^ 2 * b| ≤ B := by
    rw [abs_of_nonneg (by positivity)]
    calc r ^ 2 * b ≤ r ^ 2 * (C * (1 + s) ^ 2) := mul_le_mul_of_nonneg_left hg3 (by positivity)
      _ = C * (r * (1 + s)) ^ 2 := by ring
      _ ≤ C * 3 ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hC
      _ ≤ B := by rw [hBdef]; linarith
  have x4 : |r * b1| ≤ B := by
    rw [abs_mul, abs_of_pos hr0]
    calc r * |b1| ≤ r * (C * (1 + s)) := mul_le_mul_of_nonneg_left hg5 hr0.le
      _ = C * (r * (1 + s)) := by ring
      _ ≤ C * 3 := mul_le_mul_of_nonneg_left hrs hC
      _ ≤ B := by rw [hBdef]; linarith
  have x5 : |R * a2| ≤ B := by
    rw [abs_mul, abs_of_pos hR0]
    calc R * |a2| ≤ (1 + s) * |a2| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |a2| * (1 + s) := by ring
      _ ≤ C := hg6
      _ ≤ B := by rw [hBdef]; linarith
  have x3 : |a1| ≤ B := hg4.trans (by rw [hBdef]; linarith)
  have x6 : |b2| ≤ B := hg7.trans (by rw [hBdef]; linarith)
  have sB : ∀ {σ : ℝ}, |σ| ≤ M → |σ| ≤ B := fun h => h.trans (by rw [hBdef]; linarith)
  obtain ⟨c1, c2, c3, c4, c5⟩ := norm_bounds hB (sB hs1) (sB hs2) (sB hs3) (sB hs4) x1 x2 x3 x4 x5 x6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e : f1 * f1 * b = σ1 ^ 2 * (r ^ 2 * b) := by simp only [f1]; ring
    rw [e]; exact c1
  · have e : f1 * a + f2 * b = σ1 * (r * a) + σ2 * (r ^ 2 * b) := by simp only [f1, f2]; ring
    rw [e]; exact c2
  · have e : qP1' f1 f2 f3 a a1 b b1 * a + qP1'' f1 f2 f3 f4 a a1 a2 b b1 b2 * b =
        (r * a) * (σ2 * (r * a) + σ1 * a1 + σ3 * (r ^ 2 * b) + σ2 * (r * b1)) +
        (r ^ 2 * b) * (σ3 * (r * a) + 2 * σ2 * a1 + σ1 * (R * a2) + σ4 * (r ^ 2 * b) +
          2 * σ3 * (r * b1) + σ2 * b2) := by
      simp only [qP1', qP1'', f1, f2, f3, f4]
      linear_combination (-(r * σ1 * a2 * b)) * hrR
    rw [e]; exact c3
  · have e : qP1' f1 f2 f3 a a1 b b1 * qP1' f1 f2 f3 a a1 b b1 * b =
        (r ^ 2 * b) * (σ2 * (r * a) + σ1 * a1 + σ3 * (r ^ 2 * b) + σ2 * (r * b1)) ^ 2 := by
      simp only [qP1', f1, f2, f3]; ring
    rw [e]; exact c4
  · have e : (qΘ' f1 f2 b b1 * a + qΘ'' f1 f2 f3 b b1 b2 * b - 2 * (qP1' f1 f2 f3 a a1 b b1 * f1 * b)) / 2 =
        σ1 ^ 2 * ((r * a) * (r * b1) / 2 + (r ^ 2 * b) * b2 / 2 - (r ^ 2 * b) * a1) +
          σ1 * σ2 * (r ^ 2 * b) * (r * b1) + σ2 ^ 2 * (r ^ 2 * b) ^ 2 := by
      simp only [qΘ', qΘ'', qP1', f1, f2, f3]; ring
    rw [e]; exact c5

namespace EllData
variable (E : EllData d)

/-- **T6**: a radial exhaustion with the scale-invariant growth conditions yields a cut-off family. -/
theorem coreCut_of_radial (h : E.RadialExh) : E.CoreCut := by
  obtain ⟨ψ, α, β, hJ⟩ := h
  obtain ⟨C, hC0, hG⟩ := hJ.growth
  obtain ⟨M, hM1, b0, b1, b2, b3, b4⟩ := sig_bound
  have hψ := hJ.smooth
  refine ⟨fun n y => phiR ((n : ℝ) + 1) (ψ y), ?_⟩
  have hK0 : 0 ≤ 16 * (M + 9 * C) ^ 5 := by positivity
  refine ⟨fun n => sm_comp1 (phiR_smooth _) hψ, fun n => ?_, fun n x => ⟨sig_nonneg _, sig_le_one _⟩,
    fun x => ?_, ⟨16 * (M + 9 * C) ^ 5, fun n x => ?_⟩⟩
  · -- compact support
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine HasCompactSupport.intro (K := closure {y : Rd d | ψ y ≤ 2 * ((n : ℝ) + 1)})
      (hJ.proper _).isCompact_closure fun y hy => ?_
    have hy' : ¬ ψ y ≤ 2 * ((n : ℝ) + 1) := fun h => hy (subset_closure h)
    push Not at hy'
    show sig (ψ y / ((n : ℝ) + 1)) = 0
    refine sig_eq_zero ?_
    rw [le_div_iff₀ hR]; linarith
  · filter_upwards [eventually_ge_atTop ⌈ψ x⌉₊] with n hn
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : ψ x ≤ n := (Nat.le_ceil (ψ x)).trans (by exact_mod_cast hn)
    have hU : IsOpen {y : Rd d | ψ y < (n : ℝ) + 1} := isOpen_lt hψ.continuous continuous_const
    filter_upwards [hU.mem_nhds (show ψ x < (n : ℝ) + 1 by linarith)] with y hy
    show sig (ψ y / ((n : ℝ) + 1)) = 1
    refine sig_eq_one ?_
    rw [div_le_one hR]; exact le_of_lt hy
  · -- the bounds
    set R : ℝ := (n : ℝ) + 1 with hRdef
    have hR1 : 1 ≤ R := by rw [hRdef]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hR0 : 0 < R := by linarith
    set s : ℝ := ψ x with hsdef
    have hs0 : 0 ≤ s := hJ.nonneg x
    have e1 : deriv (phiR R) s = (1 / R) ^ 1 * deriv sig (s / R) := congrFun (iter_scale R 1) s
    have e2 : deriv (deriv (phiR R)) s = (1 / R) ^ 2 * deriv (deriv sig) (s / R) := congrFun (iter_scale R 2) s
    have e3 : deriv (deriv (deriv (phiR R))) s = (1 / R) ^ 3 * deriv (deriv (deriv sig)) (s / R) :=
      congrFun (iter_scale R 3) s
    have e4 : deriv (deriv (deriv (deriv (phiR R)))) s =
        (1 / R) ^ 4 * deriv (deriv (deriv (deriv sig))) (s / R) := congrFun (iter_scale R 4) s
    obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := E.radial_identities hJ (phiR_smooth R) x s
      ((1 / R) ^ 1 * deriv sig (s / R)) ((1 / R) ^ 2 * deriv (deriv sig) (s / R))
      ((1 / R) ^ 3 * deriv (deriv (deriv sig)) (s / R))
      ((1 / R) ^ 4 * deriv (deriv (deriv (deriv sig))) (s / R)) (α s) (deriv α s) (deriv (deriv α) s)
      (β s) (deriv β s) (deriv (deriv β) s) rfl e1.symm e2.symm e3.symm e4.symm rfl rfl rfl rfl rfl rfl
    show E.Γ (fun y => phiR R (ψ y)) (fun y => phiR R (ψ y)) x ≤ _ ∧
      |E.L (fun y => phiR R (ψ y)) x| ≤ _ ∧ |E.L (E.L (fun y => phiR R (ψ y))) x| ≤ _ ∧
      E.Γ (E.L (fun y => phiR R (ψ y))) (E.L (fun y => phiR R (ψ y))) x ≤ _ ∧
      E.G2 (fun y => phiR R (ψ y)) (fun y => phiR R (ψ y)) x ≤ _
    rw [hi1, hi2, hi3, hi4, hi5]
    by_cases hu : s / R < 1 ∨ 2 < s / R
    · have z1 : deriv sig (s / R) = 0 := sig_iter_zero 0 hu
      have z2 : deriv (deriv sig) (s / R) = 0 := sig_iter_zero 1 hu
      have z3 : deriv (deriv (deriv sig)) (s / R) = 0 := sig_iter_zero 2 hu
      have z4 : deriv (deriv (deriv (deriv sig))) (s / R) = 0 := sig_iter_zero 3 hu
      rw [z1, z2, z3, z4]
      simp only [qP1', qP1'', qΘ', qΘ'', mul_zero, zero_mul, add_zero, abs_zero, sub_zero, zero_div]
      exact ⟨by simpa using hK0, hK0, hK0, by simpa using hK0, hK0⟩
    · push Not at hu
      have hsR : R ≤ s := by
        have := hu.1; rwa [le_div_iff₀ hR0, one_mul] at this
      have hs2R : s ≤ 2 * R := by
        have := hu.2; rwa [div_le_iff₀ hR0] at this
      obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG s hs0
      have hrR : (1 / R) * R = 1 := by field_simp
      obtain ⟨q1, q2, q3, q4, q5⟩ := radial_scalar hM1 hC0 hR1 hrR (b1 _) (b2 _) (b3 _) (b4 _) hsR hs2R g1 g2 g3
        g4 g5 g6 g7
      exact ⟨(le_abs_self _).trans q1, q2, q3, (le_abs_self _).trans q4, (le_abs_self _).trans q5⟩

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
