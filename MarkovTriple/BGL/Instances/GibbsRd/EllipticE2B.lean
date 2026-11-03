import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE2A

/-!
# E2, the identity for difference quotients (Evans §6.3.1 Thm 1, Step 2, first display)

Test function `v = −D_{−t}(ζ² D_t u)` in the weak form, then integration by parts for difference quotients
(`dq_ibp_L2`) and the Leibniz rule `D_t(A g) = A(·+te) D_t g + g D_t A` (`dq_mul`).
Statement: `STATEMENTS_R16_E2.md`, E2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- **E2, Step 2 identity** (with `ψ = ζ²`, `Y = D_t u`, `Xᵢ = D_t gᵢ`, `Aᵢⱼ = w aᵢⱼ`):
`Σᵢⱼ ∫ Aᵢⱼ(·+te) Xᵢ (ψ Xⱼ + ∂ⱼψ Y) = ∫ h · D_{−t}(ψ Y) · w − Σᵢⱼ ∫ gᵢ D_tAᵢⱼ (ψ Xⱼ + ∂ⱼψ Y)`. -/
theorem dq_identity {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hh : LocL2 h) (hW : E.VeryWeakSol u h)
    (k : Fin d) (t : ℝ) {ζ : Rd d → ℝ} (hζ : Sm ζ) (hc : HasCompactSupport ζ) :
    ∑ i, ∑ j, ∫ x, (E.w (x + t • Pi.single k 1) * E.a i j (x + t • Pi.single k 1)) * dq k t (g i) x *
        (((ζ * ζ) x) * dq k t (g j) x + pderiv (ζ * ζ) j x * dq k t u x)
      = (∫ x, h x * dq k (-t) (fun y => (ζ * ζ) y * dq k t u y) x * E.w x)
        - ∑ i, ∑ j, ∫ x, g i x * dq k t (fun y => E.w y * E.a i j y) x *
          (((ζ * ζ) x) * dq k t (g j) x + pderiv (ζ * ζ) j x * dq k t u x) := by
  set ψ : Rd d → ℝ := ζ * ζ with hψ
  have hψS : Sm ψ := hζ.mul hζ
  have hψc : HasCompactSupport ψ := hc.mul_right
  set Y : Rd d → ℝ := dq k t u with hY
  set X : Fin d → Rd d → ℝ := fun i => dq k t (g i) with hX
  have hYL : LocL2 Y := locL2_dq hu k t
  have hXL : ∀ i, LocL2 (X i) := fun i => locL2_dq (hgL i) k t
  have hYw : ∀ j, WeakDeriv Y (X j) j := fun j => weakDeriv_dq (hg j) k t
  set Φ : Rd d → ℝ := fun x => ψ x * Y x with hΦ
  set Φj : Fin d → Rd d → ℝ := fun j x => ψ x * X j x + pderiv ψ j x * Y x with hΦj
  have hΦw : ∀ j, WeakDeriv Φ (Φj j) j := fun j => (hYw j).smooth_mul hψS
  have hΦL : LocL2 Φ := hYL.mul_continuous hψS.continuous
  have hΦc : HasCompactSupport Φ := hψc.mul_right
  have hΦm : MemLp Φ 2 volume := memLp_of_locL2_cs hΦL hΦc
  have hΦjL : ∀ j, LocL2 (Φj j) := fun j =>
    ((hXL j).mul_continuous hψS.continuous).add (hYL.mul_continuous (hψS.pderiv j).continuous)
  have hΦjc : ∀ j, HasCompactSupport (Φj j) := fun j => by
    have h1 : HasCompactSupport (fun x => ψ x * X j x) := hψc.mul_right
    have h2 : HasCompactSupport (fun x => pderiv ψ j x * Y x) :=
      (hψc.fderiv_apply ℝ (Pi.single j 1)).mul_right
    exact h1.add h2
  have hΦjm : ∀ j, MemLp (Φj j) 2 volume := fun j => memLp_of_locL2_cs (hΦjL j) (hΦjc j)
  -- the test function
  have key := E.weakForm_extend hu hg hgL hh hW (v := dq k (-t) Φ) (vj := fun j => dq k (-t) (Φj j))
    (memLp_dq hΦm k (-t)) (hasCompactSupport_dq hΦc k (-t)) (fun j => weakDeriv_dq (hΦw j) k (-t))
    (fun j => memLp_dq (hΦjm j) k (-t))
  -- each term of `Bf`
  set Fk : Fin d → Fin d → Rd d → ℝ := fun i j y => (E.w y * E.a i j y) * g i y with hFk
  have hFL : ∀ i j, LocL2 (Fk i j) := fun i j =>
    (hgL i).mul_continuous (E.w_smooth.continuous.mul (E.a_smooth i j).continuous)
  have hBf : E.Bf g (fun j => dq k (-t) (Φj j)) = ∑ i, ∑ j, ∫ x, Fk i j x * dq k (-t) (Φj j) x := by
    unfold Bf
    have e : ∀ x, E.w x * ∑ i, ∑ j, E.a i j x * g i x * dq k (-t) (Φj j) x =
        ∑ i, ∑ j, Fk i j x * dq k (-t) (Φj j) x := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hFk]; ring
    simp_rw [e]
    have hI : ∀ i j, Integrable (fun x => Fk i j x * dq k (-t) (Φj j) x) := fun i j =>
      integrable_locL2_mul_cs (hFL i j) (memLp_dq (hΦjm j) k (-t)) (hasCompactSupport_dq (hΦjc j) k (-t))
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hI i j
  have hibp : ∀ i j, ∫ x, Fk i j x * dq k (-t) (Φj j) x = -∫ x, dq k t (Fk i j) x * Φj j x := fun i j => by
    have := dq_ibp_L2 (hFL i j) (hΦjm j) (hΦjc j) k t
    linarith [this]
  -- Leibniz splitting
  have hsplit : ∀ i j, ∫ x, dq k t (Fk i j) x * Φj j x =
      (∫ x, (E.w (x + t • Pi.single k 1) * E.a i j (x + t • Pi.single k 1)) * dq k t (g i) x * Φj j x) +
      ∫ x, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x := fun i j => by
    have hcA : Continuous (fun x => E.w (x + t • (Pi.single k 1 : Fin d → ℝ)) *
        E.a i j (x + t • Pi.single k 1)) :=
      (E.w_smooth.continuous.comp (continuous_id.add continuous_const)).mul
        ((E.a_smooth i j).continuous.comp (continuous_id.add continuous_const))
    have hLA : LocL2 (fun x => (E.w (x + t • (Pi.single k 1 : Fin d → ℝ)) *
        E.a i j (x + t • Pi.single k 1)) * dq k t (g i) x) := (hXL i).mul_continuous hcA
    have hdA : Continuous (dq k t (fun y => E.w y * E.a i j y)) :=
      (contDiff_dq (E.w_smooth.mul (E.a_smooth i j)) k t).continuous
    have hLB : LocL2 (fun x => dq k t (fun y => E.w y * E.a i j y) x * g i x) := (hgL i).mul_continuous hdA
    have I1 := integrable_locL2_mul_cs hLA (hΦjm j) (hΦjc j)
    have I2 := integrable_locL2_mul_cs hLB (hΦjm j) (hΦjc j)
    rw [← integral_add I1 (I2.congr (Eventually.of_forall fun x => by ring))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [show Fk i j = fun y => (fun y => E.w y * E.a i j y) y * g i y from rfl, dq_mul]
    ring
  rw [hBf] at key
  simp_rw [hibp, hsplit, Finset.sum_neg_distrib] at key
  have hsum : ∀ (f1 f2 : Fin d → Fin d → ℝ), ∑ i, ∑ j, (f1 i j + f2 i j) = ∑ i, ∑ j, f1 i j + ∑ i, ∑ j, f2 i j := by
    intro f1 f2
    simp only [Finset.sum_add_distrib]
  rw [hsum] at key
  have e2 : ∀ x, h x * dq k (-t) Φ x * E.w x = h x * dq k (-t) (fun y => (ζ * ζ) y * dq k t u y) x * E.w x :=
    fun x => rfl
  simp only [e2] at key
  linarith

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
