import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Core

/-!
# S10 (ergodicity) for the Brownian triple on `(ℝ, Lebesgue)`
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

/-- du Bois-Reymond: an `L²` function with vanishing weak derivative is a.e. constant. -/
theorem dBR {u : ℝ → ℝ} (hu : MemLp u 2 volume)
    (h : ∀ φ ∈ A₀, ∫ x, u x * deriv φ x = 0) : ∃ c : ℝ, u =ᵐ[volume] fun _ => c := by
  have hI : 0 < ∫ x, chi x :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) chi_smooth.continuous
      chi_cs chi_nonneg (by rw [chi_eq_one (by simp)]; exact one_ne_zero)
  set η : ℝ → ℝ := (∫ x, chi x)⁻¹ • chi with hη
  have hηm : η ∈ A₀ := A₀.smul_mem _ chi_mem
  have hη1 : ∫ x, η x = 1 := by
    simp only [hη, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul]; field_simp
  set c : ℝ := ∫ x, u x * η x with hc
  have key : ∀ ψ ∈ A₀, ∫ x, ψ x * (u x - c) = 0 := by
    intro ψ hψ
    set θ : ℝ → ℝ := ψ - (∫ x, ψ x) • η with hθ
    have hθm : θ ∈ A₀ := A₀.sub_mem hψ (A₀.smul_mem _ hηm)
    have hθ0 : ∫ x, θ x = 0 := by
      simp only [hθ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_sub (integrable_of hψ) ((integrable_of hηm).const_mul _), integral_const_mul, hη1]
      ring
    obtain ⟨φ, hφ, hφθ⟩ := exists_antiderivative hθm hθ0
    have h1 := h φ hφ
    rw [hφθ] at h1
    have hiu : Integrable (fun x => u x * ψ x) := hu.integrable_mul (memLp_of hψ 2)
    have hiη : Integrable (fun x => u x * η x) := hu.integrable_mul (memLp_of hηm 2)
    simp only [hθ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub] at h1
    rw [integral_sub hiu (by simpa [mul_left_comm] using hiη.const_mul (∫ x, ψ x))] at h1
    have e : ∫ x, u x * ((∫ x, ψ x) * η x) = (∫ x, ψ x) * c := by
      rw [hc, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [e] at h1
    have : ∫ x, ψ x * (u x - c) = (∫ x, u x * ψ x) - c * ∫ x, ψ x := by
      have e : (fun x => ψ x * (u x - c)) = fun x => u x * ψ x - c * ψ x := by
        funext x; ring
      rw [e, integral_sub hiu ((integrable_of hψ).const_mul c), integral_const_mul]
    rw [this]; linarith
  refine ⟨c, ?_⟩
  have hloc : LocallyIntegrable (fun x => u x - c) volume :=
    (hu.locallyIntegrable (by norm_num)).sub (locallyIntegrable_const c)
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg hgs => by
    have := key g (mem_A₀.2 ⟨hg, hgs⟩)
    simpa [smul_eq_mul] using this)
  filter_upwards [this] with x hx
  linarith

/-- **S10** for the Brownian triple. -/
theorem ergodic_lebesgue (u : Lp ℝ 2 (volume : Measure ℝ)) (hu : u ∈ lebesgueDiffusion.generator.domain)
    (hG : lebesgueDiffusion.generator ⟨u, hu⟩ = 0) : ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[volume] fun _ => c := by
  refine (lebesgueDiffusion.ergodic_iff_energy.2 ?_) u hu hG
  intro v hv
  obtain ⟨a, h1, -, h3⟩ := lebesgueDiffusion.formDomain_approx v
  rw [hv] at h3
  refine dBR (Lp.memLp (v : Lp ℝ 2 (volume : Measure ℝ))) (fun φ hφ => ?_)
  have hφ' := deriv_mem hφ
  -- ⟪v, [φ']⟫ = 0
  have hin : Tendsto (fun n => inner ℝ (lebesgueDiffusion.cls (a n))
      (lebesgueDiffusion.cls ⟨deriv φ, hφ'⟩)) atTop
      (𝓝 (inner ℝ (v : Lp ℝ 2 (volume : Measure ℝ)) (lebesgueDiffusion.cls ⟨deriv φ, hφ'⟩))) :=
    h1.inner tendsto_const_nhds
  have hbound : ∀ n, |inner ℝ (lebesgueDiffusion.cls (a n))
      (lebesgueDiffusion.cls ⟨deriv φ, hφ'⟩)| ≤
      Real.sqrt (lebesgueDiffusion.ℰ (a n) (a n)) * ‖lebesgueDiffusion.cls ⟨φ, hφ⟩‖ := by
    intro n
    have hd := deriv_mem (a n).2
    have e1 : inner ℝ (lebesgueDiffusion.cls (a n)) (lebesgueDiffusion.cls ⟨deriv φ, hφ'⟩) =
        -inner ℝ (lebesgueDiffusion.cls ⟨deriv (a n).1, hd⟩) (lebesgueDiffusion.cls ⟨φ, hφ⟩) := by
      rw [inner_cls_cls _ _ (a n).2 hφ', inner_cls_cls _ _ hd hφ]
      exact ibp_cs (smooth (a n).2) (smooth hφ) (Or.inl (cs (a n).2))
    have e2 : ‖lebesgueDiffusion.cls ⟨deriv (a n).1, hd⟩‖ =
        Real.sqrt (lebesgueDiffusion.ℰ (a n) (a n)) := by
      rw [← Real.sqrt_sq (norm_nonneg _), sq, ← real_inner_self_eq_norm_mul_norm,
        inner_cls_cls _ _ hd hd]
      rfl
    rw [e1, abs_neg, ← e2]
    exact abs_real_inner_le_norm _ _
  have h0 : Tendsto (fun n => inner ℝ (lebesgueDiffusion.cls (a n))
      (lebesgueDiffusion.cls ⟨deriv φ, hφ'⟩)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => by simpa using hbound n) ?_
    have := ((Real.continuous_sqrt.tendsto 0).comp h3).mul_const
      ‖lebesgueDiffusion.cls ⟨φ, hφ⟩‖
    simpa using this
  have hz := tendsto_nhds_unique hin h0
  rw [L2_inner_eq] at hz
  rw [← hz]
  refine integral_congr_ae ?_
  filter_upwards [lebesgueDiffusion.coeFn_cls ⟨deriv φ, hφ'⟩] with x hx
  rw [hx]

end MarkovTriple.BGL.Lebesgue
