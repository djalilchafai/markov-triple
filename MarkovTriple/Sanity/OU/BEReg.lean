import MarkovTriple.Sanity.OU.MehlerEq
import MarkovTriple.FunctionalInequalities.BEStable

/-! # OU (Part 19): `BEReg` for `ψ ∘ G`, `G` a Schwartz function, `ψ` smooth

Everything is expressed inside Mathlib's Schwartz space: `(ψ ∘ G)' = (ψ' ∘ G) · G'` is Schwartz
(`ψ' ∘ G` has temperate growth since `G` is bounded), and `L`, `Γ` map the relevant derivatives
to Schwartz functions, hence bounded. -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Real SchwartzMap

namespace MarkovTriple.Sanity.OU

open SchwartzMap

/-- `V ↦ V' − x V` on Schwartz space -/
noncomputable def Ls (W : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℝ) :=
  derivCLM ℝ ℝ W - smulLeftCLM ℝ (fun x : ℝ => x) W

lemma Ls_apply (W : 𝓢(ℝ, ℝ)) (x : ℝ) : Ls W x = deriv W x - x * W x := by
  simp [Ls, smulLeftCLM_apply_apply Function.HasTemperateGrowth.id']

lemma Lo_eq_Ls {u : ℝ → ℝ} {W : 𝓢(ℝ, ℝ)} (h : deriv u = ⇑W) : Lo u = ⇑(Ls W) := by
  funext x
  rw [Ls_apply, Lo, h]

lemma memLp_top_schwartz (V : 𝓢(ℝ, ℝ)) : MemLp (⇑V) ∞ γ := by
  refine memLp_top_of_bound V.continuous.aestronglyMeasurable (SchwartzMap.seminorm ℝ 0 0 V)
    (ae_of_all _ fun x => ?_)
  have := V.le_seminorm' ℝ 0 0 x
  simpa using this

lemma memLp_two_schwartz (V : 𝓢(ℝ, ℝ)) : MemLp (⇑V) 2 γ :=
  (memLp_top_schwartz V).mono_exponent (by simp)

/-- **`BEReg` for `ψ ∘ G`**, `G` Schwartz, `ψ` smooth. -/
theorem beReg_comp_schwartz (G : 𝓢(ℝ, ℝ)) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    BE.BEReg ouFull (fun x => ψ (G x)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, |G x| ≤ C :=
    ⟨SchwartzMap.seminorm ℝ 0 0 G, fun x => by simpa using G.le_seminorm' ℝ 0 0 x⟩
  -- `ψ' ∘ G` has temperate growth
  set bump : ContDiffBump (0 : ℝ) := ⟨|C| + 1, |C| + 2, by positivity, by linarith⟩ with hbump
  have hψ1 : Function.HasTemperateGrowth (fun y => bump y * deriv ψ y) := by
    refine HasCompactSupport.hasTemperateGrowth ?_ ?_
    · exact bump.hasCompactSupport.mul_right
    · exact (bump.contDiff).mul ((contDiff_infty_iff_deriv.1 hψ).2)
  have hT : Function.HasTemperateGrowth (fun x => deriv ψ (G x)) := by
    have := hψ1.comp G.hasTemperateGrowth
    convert this using 1
    funext x
    simp only [Function.comp]
    rw [bump.one_of_mem_closedBall, one_mul]
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact (hC x).trans (by simp [hbump]; linarith [le_abs_self C])
  set W : 𝓢(ℝ, ℝ) := smulLeftCLM ℝ (fun x => deriv ψ (G x)) (derivCLM ℝ ℝ G) with hW
  have hWx : ∀ x, W x = deriv ψ (G x) * deriv G x := fun x => by
    rw [hW, smulLeftCLM_apply_apply hT]; rfl
  have hu' : deriv (fun x => ψ (G x)) = ⇑W := by
    funext x
    have h1 : HasDerivAt ψ (deriv ψ (G x)) (G x) :=
      ((hψ.differentiable (by simp)) (G x)).hasDerivAt
    have h2 : HasDerivAt (⇑G) (deriv G x) x := (G.differentiableAt).hasDerivAt
    rw [hWx]
    exact (h1.comp x h2).deriv
  -- bounded
  obtain ⟨K, hK⟩ : ∃ K, ∀ y ∈ Metric.closedBall (0 : ℝ) C, ‖ψ y‖ ≤ K :=
    (isCompact_closedBall (0 : ℝ) C).exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hbdd : MemLp (fun x => ψ (G x)) ∞ γ :=
    memLp_top_of_bound (hψ.continuous.comp G.continuous).aestronglyMeasurable K
      (ae_of_all _ fun x => hK _ (by rw [mem_closedBall_zero_iff, Real.norm_eq_abs]; exact hC x))
  have hL : Lo (fun x => ψ (G x)) = ⇑(Ls W) := Lo_eq_Ls hu'
  have hΓ : Go (fun x => ψ (G x)) (fun x => ψ (G x)) =
      ⇑(smulLeftCLM ℝ (⇑W) W) := by
    funext x
    rw [smulLeftCLM_apply_apply W.hasTemperateGrowth]
    simp [Go, hu']
  have hLL : Lo (Lo (fun x => ψ (G x))) = ⇑(Ls (derivCLM ℝ ℝ (Ls W))) := by
    rw [hL]; exact Lo_eq_Ls rfl
  have hLΓ : Lo (Go (fun x => ψ (G x)) (fun x => ψ (G x))) =
      ⇑(Ls (derivCLM ℝ ℝ (smulLeftCLM ℝ (⇑W) W))) := by
    rw [hΓ]; exact Lo_eq_Ls rfl
  refine ⟨hbdd, ?_, ?_, ?_, ?_⟩
  · show MemLp (Lo _) ∞ γ
    rw [hL]; exact memLp_top_schwartz _
  · show MemLp (Go _ _) ∞ γ
    rw [hΓ]; exact memLp_top_schwartz _
  · show MemLp (Lo (Lo _)) 2 γ
    rw [hLL]; exact memLp_two_schwartz _
  · show MemLp (Lo (Go _ _)) 2 γ
    rw [hLΓ]; exact memLp_two_schwartz _

end MarkovTriple.Sanity.OU
