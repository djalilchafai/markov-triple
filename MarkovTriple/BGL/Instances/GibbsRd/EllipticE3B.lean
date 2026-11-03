import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE3A

/-!
# E3, part B: the differentiated very weak equation

Statements: `STATEMENTS_R16_E3.md` (E3.1).  Evans §6.3.1 Thm 2 (differentiate the equation in direction `m`):
if `L u = h` in the very weak sense, `u ∈ H²_loc` and `∂_m h ∈ L²_loc`, then `∂_m u` solves the very weak equation with right-hand side
`h' = w⁻¹(∂_m(w h) − Σᵢⱼ ∂ⱼ(Bᵢⱼ ∂ᵢu))`, `Bᵢⱼ = ∂_m(w aᵢⱼ)`.  Only weak-derivative hypotheses are used (no `L²` assumptions).
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- the new right-hand side `h'` (E3.1) -/
noncomputable def hprime (m : Fin d) (h H : Rd d → ℝ) (g : Fin d → Rd d → ℝ) (G : Fin d → Fin d → Rd d → ℝ) :
    Rd d → ℝ :=
  fun x => (E.w x)⁻¹ * (E.w x * H x + pderiv E.w m x * h x -
    ∑ i, ∑ j, (E.Bc m i j x * G i j x + pderiv (E.Bc m i j) j x * g i x))

lemma wL_mem {b : Rd d → ℝ} (hb : b ∈ A₀ d) : (fun y => E.w y * E.L b y) ∈ A₀ d :=
  ⟨E.w_smooth.mul (E.sm_L hb.1), hcs_of_factor (E.hcs_L hb.2) fun x hx => by simp [hx]⟩

/-- **E3.1**: the derivative `g m = ∂_m u` solves the very weak equation with right-hand side `h'`. -/
theorem veryWeakSol_deriv {u h H : Rd d → ℝ} {g : Fin d → Rd d → ℝ} {G : Fin d → Fin d → Rd d → ℝ}
    (m : Fin d) (hg : ∀ i, WeakDeriv u (g i) i) (hG : ∀ i j, WeakDeriv (g i) (G i j) j)
    (hH : WeakDeriv h H m) (hW : E.VeryWeakSol u h) :
    E.VeryWeakSol (g m) (E.hprime m h H g G) := by
  intro a ha
  obtain ⟨hs, hc⟩ := ha
  have hu : LocallyIntegrable u := (hg m).1
  have I : ∀ {f c : Rd d → ℝ}, LocallyIntegrable f → Sm c → HasCompactSupport c →
      Integrable (fun x => f x * c x) := fun hf hc' hs' => integrable_mul_cs hf hc'.continuous hs'
  have hma : pderiv a m ∈ A₀ d := A₀.pderiv_mem ⟨hs, hc⟩ m
  have hF := E.wL_mem (⟨hs, hc⟩ : a ∈ A₀ d)
  have hFm := E.wL_mem hma
  have hQs := fun i => E.sm_Qf m hs i
  have hQc := fun i => E.hcs_Qf m hc i
  have hdQs : ∀ i, Sm (pderiv (E.Qf m a i) i) := fun i => (hQs i).pderiv i
  have hdQc : ∀ i, HasCompactSupport (pderiv (E.Qf m a i) i) := fun i => (hQc i).fderiv_apply ℝ (Pi.single i 1)
  -- (1) integrate by parts in direction m against `F = w L a`
  have s1 : ∫ x, u x * pderiv (fun y => E.w y * E.L a y) m x = -∫ x, g m x * (E.w x * E.L a x) :=
    (hg m).2.2 _ hF.1 hF.2
  have s1' : ∫ x, u x * pderiv (fun y => E.w y * E.L a y) m x =
      (∑ i, ∫ x, u x * pderiv (E.Qf m a i) i x) + ∫ x, u x * (E.w x * E.L (pderiv a m) x) := by
    have e : ∀ x, u x * pderiv (fun y => E.w y * E.L a y) m x =
        ∑ i, u x * pderiv (E.Qf m a i) i x + u x * (E.w x * E.L (pderiv a m) x) := by
      intro x; rw [E.comm_identity m hs x, mul_add, Finset.mul_sum]
    simp_rw [e]
    rw [integral_add (integrable_finsetSum _ fun i _ => I hu (hdQs i) (hdQc i)) (I hu hFm.1 hFm.2),
      integral_finsetSum _ fun i _ => I hu (hdQs i) (hdQc i)]
  have s2 : ∀ i, ∫ x, u x * pderiv (E.Qf m a i) i x = -∫ x, g i x * E.Qf m a i x := fun i =>
    (hg i).2.2 _ (hQs i) (hQc i)
  have s3 : ∫ x, u x * (E.w x * E.L (pderiv a m) x) = ∫ x, h x * pderiv a m x * E.w x := by
    rw [← hW _ hma]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- (2) the Q-terms
  have hGint : ∀ i j, Integrable (fun x => (E.Bc m i j x * G i j x + pderiv (E.Bc m i j) j x * g i x) * a x) :=
    fun i j => by
      have := ((hG i j).smooth_mul (E.sm_Bc m i j)).2.1
      exact I this hs hc
  have s4 : ∀ i, ∫ x, g i x * E.Qf m a i x = -∑ j, ∫ x, (E.Bc m i j x * G i j x + pderiv (E.Bc m i j) j x * g i x) * a x := by
    intro i
    have e : ∀ x, g i x * E.Qf m a i x = ∑ j, (E.Bc m i j x * g i x) * pderiv a j x := by
      intro x; unfold Qf; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e]
    have hint : ∀ j, Integrable (fun x => (E.Bc m i j x * g i x) * pderiv a j x) := fun j => by
      have := ((hG i j).smooth_mul (E.sm_Bc m i j)).1
      exact I this (hs.pderiv j) (hc.fderiv_apply ℝ (Pi.single j 1))
    rw [integral_finsetSum _ fun j _ => hint j, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => ((hG i j).smooth_mul (E.sm_Bc m i j)).2.2 a hs hc
  -- (3) the h-term
  have s5 : ∫ x, h x * pderiv a m x * E.w x = -∫ x, (E.w x * H x + pderiv E.w m x * h x) * a x := by
    have := (hH.smooth_mul E.w_smooth).2.2 a hs hc
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show _ = E.w x * h x * pderiv a m x
      ring)
  have hHint : Integrable (fun x => (E.w x * H x + pderiv E.w m x * h x) * a x) :=
    I (hH.smooth_mul E.w_smooth).2.1 hs hc
  -- assemble
  have hL : ∫ x, g m x * E.L a x * E.w x = ∫ x, g m x * (E.w x * E.L a x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hR : ∫ x, E.hprime m h H g G x * a x * E.w x =
      (∫ x, (E.w x * H x + pderiv E.w m x * h x) * a x) -
        ∑ i, ∑ j, ∫ x, (E.Bc m i j x * G i j x + pderiv (E.Bc m i j) j x * g i x) * a x := by
    have e : ∀ x, E.hprime m h H g G x * a x * E.w x = (E.w x * H x + pderiv E.w m x * h x) * a x -
        ∑ i, ∑ j, (E.Bc m i j x * G i j x + pderiv (E.Bc m i j) j x * g i x) * a x := by
      intro x
      have hw := (E.w_pos x).ne'
      unfold hprime
      simp only [← Finset.sum_mul]
      field_simp
    simp_rw [e]
    rw [integral_sub hHint (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hGint i j),
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hGint i j]
    congr 1
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hGint i j
  rw [hL, hR]
  simp only [s2, s3, s4, s5, Finset.sum_neg_distrib] at s1'
  linarith

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
