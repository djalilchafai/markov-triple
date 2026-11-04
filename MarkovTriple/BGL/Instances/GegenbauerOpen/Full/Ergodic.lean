import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.RegLocal
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.NotL2
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Theory.Conservation.Hilbert

/-!
# Ergodicity (S10) of the zonal Gegenbauer triple, from interior regularity and the limit-point endpoint (R23-G2)

`u ∈ 𝒟(L)`, `L u = 0` ⇒ weak equation `∫ u L a dμ = 0` for `a ∈ C_c^∞((-1,1))` ⇒ (`go_reg_C1`) `u = U` a.e. with
`(1-x²)² U' = c` ⇒ (`go_not_integrable_sq`, `u ∈ L²`) `c = 0` ⇒ `U` constant.  F10 is not used.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal LinearPMap

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open MarkovTriple.BGL

/-- the weak equation for `u ∈ 𝒟(L)` with `L u = 0`. -/
lemma go_weak_of_generator_zero (u : Lp ℝ 2 goDiff.μ) (hu : u ∈ goDiff.generator.domain)
    (hGu : goDiff.generator ⟨u, hu⟩ = 0) :
    ∀ a ∈ goA₀, ∫ x, (u : ℝ → ℝ) x * goL a x ∂goμ = ∫ x, (fun _ : ℝ => (0 : ℝ)) x * a x ∂goμ := by
  intro a ha
  have hs := Hilbert.FormData.generator_symm (DiffusionTriple.formData goDiff) hu
    (DiffusionTriple.cls_mem_generator_domain goDiff ⟨a, ha⟩)
  have hGa := DiffusionTriple.generator_cls goDiff ⟨a, ha⟩
    (DiffusionTriple.cls_mem_generator_domain goDiff ⟨a, ha⟩)
  change inner ℝ (goDiff.generator ⟨u, hu⟩) (goDiff.cls ⟨a, ha⟩) =
    inner ℝ u (goDiff.generator ⟨goDiff.cls ⟨a, ha⟩,
      DiffusionTriple.cls_mem_generator_domain goDiff ⟨a, ha⟩⟩) at hs
  rw [hGa, hGu, inner_zero_left, L2_inner_eq] at hs
  simp only [zero_mul, integral_zero]
  rw [hs]
  exact (integral_congr_ae (by
    filter_upwards [DiffusionTriple.coeFn_Lcls goDiff ⟨a, ha⟩] with x hx
    rw [hx])).symm

/-- **S10 for `goDiff`**: ergodicity. -/
theorem go_ergodic : ∀ (u : Lp ℝ 2 goDiff.μ) (hu : u ∈ goDiff.generator.domain),
    goDiff.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[goDiff.μ] fun _ => c := by
  intro u hu hGu
  have hweak := go_weak_of_generator_zero u hu hGu
  have hu1 : Integrable (u : ℝ → ℝ) goμ := (Lp.memLp u).integrable (by norm_num)
  obtain ⟨U, c, hU, huae, hform⟩ := go_reg_C1 (h := fun _ => (0 : ℝ)) hu1 (integrable_zero _ _ _) hweak
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, (1 - x ^ 2) ^ 2 * deriv U x = c := fun x hx => by
    simpa using hform x hx
  have hc : c = 0 := by
    by_contra hc
    refine go_not_integrable_sq hc hU hd ?_
    have h2 : Integrable (fun x => (u : ℝ → ℝ) x ^ 2) goμ := (Lp.memLp u).integrable_sq
    refine h2.congr ?_
    filter_upwards [huae] with x hx
    rw [hx]
  subst hc
  have hderiv : ∀ x ∈ Ioo (-1 : ℝ) 1, deriv U x = 0 := fun x hx => by
    have h := hd x hx
    have hne : (1 - x ^ 2) ^ 2 ≠ 0 := by
      have : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      positivity
    simpa [hne] using h
  have hdiff : DifferentiableOn ℝ U (Ioo (-1 : ℝ) 1) := hU.differentiableOn (by simp)
  have hconst : ∀ x ∈ Ioo (-1 : ℝ) 1, U x = U 0 := fun x hx =>
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected hdiff
      (fun y hy => by simpa using hderiv y hy) hx ⟨by norm_num, by norm_num⟩
  refine ⟨U 0, ?_⟩
  filter_upwards [huae, ae_go (p := fun x => x ∈ Ioo (-1 : ℝ) 1) fun x hx => hx] with x h1 h2
  rw [h1, hconst x h2]

end MarkovTriple.BGL.Instances.GegenbauerOpen
