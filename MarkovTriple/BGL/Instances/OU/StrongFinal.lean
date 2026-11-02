import Mathlib
import MarkovTriple.BGL.Instances.OU.StrongMain

/-!
# OU strong gradient bound (Part 3): `ouFull.StrongInterpolation` and Thm 3.3.18 for OU, unconditionally
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

variable {ε : ℝ}

lemma strongD_eq (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ OA₀) (τ x : ℝ) :
    ouFull.strongD ε (m0 f τ) x = sD ε f τ x := by
  have hψd : Differentiable ℝ (psiS ε) := (psiS_smooth hε).differentiable (by simp)
  have hΓ : ouFull.toDiffusionTriple.ΓA (m0 f τ) (m0 f τ) = fun y => m1 f τ y * m1 f τ y :=
    ΓA_eq_of_hasDeriv (sm_m0 hf _) (d0x hf _)
  -- derivatives of `F = ψ ∘ q`
  set Q : ℝ → ℝ := fun y => m1 f τ y * m1 f τ y with hQ
  set Q1 : ℝ → ℝ := fun y => m2 f τ y * m1 f τ y + m1 f τ y * m2 f τ y with hQ1
  set Q2 : ℝ → ℝ := fun y => (m3 f τ y * m1 f τ y + m2 f τ y * m2 f τ y) +
    (m2 f τ y * m2 f τ y + m1 f τ y * m3 f τ y) with hQ2
  have hdQ : ∀ y, HasDerivAt Q (Q1 y) y := fun y => (d1x hf τ y).mul (d1x hf τ y)
  have hdQ1 : ∀ y, HasDerivAt Q1 (Q2 y) y := fun y =>
    ((d2x hf τ y).mul (d1x hf τ y)).add ((d1x hf τ y).mul (d2x hf τ y))
  set G1 : ℝ → ℝ := fun y => deriv (psiS ε) (Q y) * Q1 y with hG1
  set G2 : ℝ → ℝ := fun y => deriv (deriv (psiS ε)) (Q y) * Q1 y * Q1 y +
    deriv (psiS ε) (Q y) * Q2 y with hG2
  have hdG : ∀ y, HasDerivAt (fun y => psiS ε (Q y)) (G1 y) y := fun y =>
    (hψd (Q y)).hasDerivAt.comp y (hdQ y)
  have hdG1 : ∀ y, HasDerivAt G1 (G2 y) y := fun y => by
    have h1 : HasDerivAt (deriv (psiS ε)) (deriv (deriv (psiS ε)) (Q y)) (Q y) :=
      (((contDiff_deriv_psiS hε).differentiable (by simp)) (Q y)).hasDerivAt
    have := (h1.comp y (hdQ y)).mul (hdQ1 y)
    refine (show HasDerivAt G1 _ y from this).congr_deriv ?_
    simp only [hG2, Function.comp_apply]
  have hF1 : deriv (fun y => psiS ε (Q y)) = G1 := funext fun y => (hdG y).deriv
  -- Lo of g and Γ(g, Lg)
  have hLg : Lo (m0 f τ) = fun y => m2 f τ y - y * m1 f τ y := by
    funext y
    simp only [Lo, deriv_m0 hf, deriv_m1 hf]
  have hdLg : ∀ y, HasDerivAt (fun y => m2 f τ y - y * m1 f τ y)
      (m3 f τ y - (1 * m1 f τ y + y * m2 f τ y)) y := fun y =>
    (d2x hf τ y).sub ((hasDerivAt_id y).mul (d1x hf τ y))
  have hsmLg : Sm (Lo (m0 f τ)) := sm_Lo (sm_m0 hf τ)
  have hΓLg : ouFull.toDiffusionTriple.ΓA (m0 f τ) (Lo (m0 f τ)) =
      Go (m0 f τ) (Lo (m0 f τ)) := ouDiff_ΓA (sm_m0 hf τ) hsmLg
  have hderLg : deriv (Lo (m0 f τ)) x = m3 f τ x - (1 * m1 f τ x + x * m2 f τ x) := by
    rw [hLg]; exact (hdLg x).deriv
  unfold FullTriple.strongD
  show ouFull.L (fun y => psiS ε (ouFull.toDiffusionTriple.ΓA (m0 f τ) (m0 f τ) y)) x -
    2 * deriv (psiS ε) (ouFull.toDiffusionTriple.ΓA (m0 f τ) (m0 f τ) x) *
      ouFull.toDiffusionTriple.ΓA (m0 f τ) (ouFull.L (m0 f τ)) x = _
  rw [hΓ]
  have hL : ouFull.L = Lo := rfl
  have hGL : ouFull.toDiffusionTriple.ΓA (m0 f τ) (ouFull.L (m0 f τ)) x =
      m1 f τ x * (m3 f τ x - (1 * m1 f τ x + x * m2 f τ x)) := by
    rw [hL]
    have := congrFun hΓLg x
    refine this.trans ?_
    simp only [Go, deriv_m0 hf, hderLg]
  rw [hGL, hL]
  simp only [Lo]
  rw [hF1, (hdG1 x).deriv]
  simp only [hG1, hG2, hQ1, hQ2, hQ, sD]
  ring

/-- **The strong-gradient regularity hypothesis holds for the OU triple.** -/
theorem ouFull_StrongInterpolation : ouFull.StrongInterpolation where
  continuousOn := fun ε hε f h _ t =>
    (sPhi_continuousOn hε h.2 f.2 (t : ℝ)).congr fun s hs => strongPhi_eq hε f h t hs
  hasDerivAt := fun ε hε f h _ t s hs => by
    obtain ⟨i1, i2, hd⟩ := sPhi_hasDerivAt hε h.2 f.2 hs
    have hP : ouFull.Pt s.toNNReal h = m0 h.1 s := Pt_eq_m0 h hs.1.le
    have hr : 0 ≤ (t : ℝ) - s := sub_nonneg.2 hs.2.le
    have hQ : ouFull.Pt ((t : ℝ) - s).toNNReal f = m0 f.1 ((t : ℝ) - s) := Pt_eq_m0 f hr
    have hΓ : ouFull.toDiffusionTriple.ΓA (m0 f.1 (t - s)) (m0 f.1 (t - s)) =
        fun x => m1 f.1 (t - s) x * m1 f.1 (t - s) x :=
      ΓA_eq_of_hasDeriv (sm_m0 f.2 _) (d0x f.2 _)
    have hD : ouFull.strongD ε (m0 f.1 (t - s)) = sD ε f.1 (t - s) :=
      funext fun x => strongD_eq hε f.2 _ x
    rw [hP, hQ, hD]
    refine ⟨?_, i2, ?_⟩
    · show Integrable (fun x => m0 h.1 s x * psiS ε
        (ouFull.toDiffusionTriple.ΓA (m0 f.1 (t - s)) (m0 f.1 (t - s)) x)) γ
      rw [hΓ]; exact i1
    · refine hd.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs' using
        strongPhi_eq hε f h t ⟨hs'.1.le, hs'.2.le⟩

/-- **Strong gradient bound for the OU triple** (BGL Thm 3.3.18, `ρ = 1`, unconditional):
`√Γ(P_t f) ≤ e^{-t} P_t(√Γ f)` a.e., for `f ∈ C_c^∞`. -/
theorem ouFull_strong_gradient_bound (f : ouFull.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂ouFull.μ, Real.sqrt (ouFull.toDiffusionTriple.ΓA (ouFull.Pt t f) (ouFull.Pt t f) x) ≤
      Real.exp (-1 * t) *
        (ouFull.toDiffusionTriple.semigroup t (ouFull.sqrtΓcls f) : Lp ℝ 2 ouFull.μ) x :=
  FullTriple.strong_gradient_bound ouFull_CD zero_le_one ouFull_StrongInterpolation f t

end MarkovTriple.BGL.Instances.OU

#print axioms MarkovTriple.BGL.Instances.OU.ouFull_StrongInterpolation
#print axioms MarkovTriple.BGL.Instances.OU.ouFull_strong_gradient_bound
