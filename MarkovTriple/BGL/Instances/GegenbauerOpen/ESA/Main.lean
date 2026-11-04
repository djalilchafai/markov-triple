import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Diffusion
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.Weyl
import MarkovTriple.BGL.Instances.GegenbauerOpen.ESA.Regularity
import MarkovTriple.BGL.Theory.ESAOne

/-!
# F10 (essential self-adjointness) for the zonal Gegenbauer triple `goDiff` (`λ = 3/2`) on `(-1,1)`

`go_esaProp : goDiff.ESAProp`.  See `STATEMENTS_R23_G1.md`.  Route (B): `(1 - L) C_c^∞` is dense in `L²(μ)` (a deficiency
vector is a weak solution of `(L - 1) u = 0`, hence regular (`weak_regular`) and then zero by the Weyl limit-point argument
(`weyl`)), and density of `(1 - L)𝒜₀` gives `ESAProp` abstractly (`esaProp_of_orth`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace DiffusionTriple

/-- **Abstract reduction**: if `(1 - L)𝒜₀` is dense in `L²(μ)`, then `𝒜₀` is a core for the Friedrichs generator
(`ESAProp`).  (The second half of `core_of_invariant`.) -/
theorem esaProp_of_orth (T : DiffusionTriple E)
    (h : ∀ w : Lp ℝ 2 T.μ, (∀ a : T.A₀, inner ℝ (T.cls a - T.Lcls a) w = 0) → w = 0) :
    T.ESAProp := by
  intro u hu
  set S := formData T with hS
  let M : Submodule ℝ (Lp ℝ 2 T.μ) := (LinearMap.range (clsₗ T - Lclsₗ T))
  have hM : M.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    exact h w (fun a => hw _ ⟨a, rfl⟩)
  have hdense : Dense (M : Set (Lp ℝ 2 T.μ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 hM
  set g : Lp ℝ 2 T.μ := u - S.generator ⟨u, hu⟩ with hg
  obtain ⟨m, hmM, hmg⟩ := mem_closure_iff_seq_limit.1 (hdense.closure_eq ▸ Set.mem_univ g)
  have hm : ∀ n, ∃ a : T.A₀, T.cls a - T.Lcls a = m n := by
    intro n
    obtain ⟨a, ha⟩ := hmM n
    exact ⟨a, ha⟩
  choose a ha using hm
  have hRu : S.R g = u := (S.generator_apply_eq_iff hu _).1 rfl
  have h1 : Tendsto (fun n => T.cls (a n)) atTop (𝓝 u) := by
    have : Tendsto (fun n => S.R (m n)) atTop (𝓝 (S.R g)) := (S.R.continuous.tendsto g).comp hmg
    rw [hRu] at this
    refine this.congr (fun n => ?_)
    rw [← ha n]; exact R_cls_sub T (a n)
  refine ⟨a, h1, ?_⟩
  have h2 : Tendsto (fun n => T.cls (a n) - m n) atTop (𝓝 (u - g)) := h1.sub hmg
  have e : u - g = S.generator ⟨u, hu⟩ := by rw [hg]; abel
  rw [e] at h2
  refine h2.congr (fun n => ?_)
  rw [← ha n]; abel

end DiffusionTriple

end MarkovTriple.BGL

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open ESA

/-- **(iii)** deficiency vectors vanish: `(1 - L) C_c^∞((-1,1))` is dense in `L²(goμ)`. -/
theorem go_orth_zero (w : Lp ℝ 2 goμ)
    (h : ∀ a : goDiff.A₀, inner ℝ (goDiff.cls a - goDiff.Lcls a) w = 0) : w = 0 := by
  set u : ℝ → ℝ := (w : ℝ → ℝ) with hu
  have hmeasμ : AEStronglyMeasurable u goμ := Lp.aestronglyMeasurable w
  have hac : volume.restrict (Ioo (-1:ℝ) 1) ≪ goμ :=
    withDensity_absolutelyContinuous' (by fun_prop : Measurable _).aemeasurable
      ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => by
        have : 0 < 3 / 4 * (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
        exact (ENNReal.ofReal_pos.2 this).ne'))
  have hmeas : AEStronglyMeasurable u (volume.restrict (Ioo (-1:ℝ) 1)) := hmeasμ.mono_ac hac
  have hsq : Integrable (fun x => u x ^ 2) goμ := (Lp.memLp w).integrable_sq
  have h1 : Integrable (fun x => (Real.toNNReal (3 / 4 * (1 - x ^ 2))) • u x ^ 2)
      (volume.restrict (Ioo (-1:ℝ) 1)) :=
    (integrable_withDensity_iff_integrable_smul (f := fun x => Real.toNNReal (3 / 4 * (1 - x ^ 2)))
      (by fun_prop) (g := fun x => u x ^ 2)).1 hsq
  have hint : IntegrableOn (fun x => (1 - x ^ 2) * u x ^ 2) (Ioo (-1:ℝ) 1) := by
    refine (h1.const_mul (4 / 3)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have : 0 ≤ 3 / 4 * (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
    simp only [NNReal.smul_def, Real.coe_toNNReal _ this, smul_eq_mul]
    ring
  have hweak : ∀ f ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, u x * ((1 - x ^ 2) * (f x - goL f x)) = 0 := by
    intro f hf
    have h0 := h ⟨f, hf⟩
    rw [L2_inner_eq] at h0
    have e1 : ∫ x, (goDiff.cls ⟨f, hf⟩ - goDiff.Lcls ⟨f, hf⟩ : Lp ℝ 2 goμ) x * w x ∂goμ =
        ∫ x, (f x - goL f x) * u x ∂goμ := by
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (goDiff.cls ⟨f, hf⟩) (goDiff.Lcls ⟨f, hf⟩),
        DiffusionTriple.coeFn_cls goDiff ⟨f, hf⟩, DiffusionTriple.coeFn_Lcls goDiff ⟨f, hf⟩]
        with x h2 h3 h4
      rw [h2]
      simp only [Pi.sub_apply, h3, h4]
      rfl
    rw [e1] at h0
    rw [integral_goμ (fun x hx => by
      simp [zero_off_go hf hx, zero_off_go (goL_mem hf) hx])] at h0
    have e2 : ∫ x in Ioo (-1:ℝ) 1, (3 / 4 * (1 - x ^ 2)) * ((f x - goL f x) * u x) = 0 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact h0
      · intro x hx
        simp [zero_off_go hf hx, zero_off_go (goL_mem hf) hx]
    have e3 : ∫ x in Ioo (-1:ℝ) 1, u x * ((1 - x ^ 2) * (f x - goL f x)) =
        4 / 3 * ∫ x in Ioo (-1:ℝ) 1, (3 / 4 * (1 - x ^ 2)) * ((f x - goL f x) * u x) := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [e3, e2, mul_zero]
  obtain ⟨v, F, hv, hF, hae⟩ := weak_regular u hint hmeas hweak
  have hintv : IntegrableOn (fun x => (1 - x ^ 2) * v x ^ 2) (Ioo (-1:ℝ) 1) := by
    refine hint.congr_fun_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have hv0 := weyl v F hv hF hintv
  have hu0 : u =ᵐ[volume.restrict (Ioo (-1:ℝ) 1)] 0 := by
    filter_upwards [hae, (ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall hv0)] with x h1 h2
    rw [h1, h2]; rfl
  have hu0' : u =ᵐ[goμ] 0 := withDensity_absolutelyContinuous _ _ hu0
  exact Lp.eq_zero_iff_ae_eq_zero.2 hu0'

/-- **F10 for the zonal Gegenbauer triple `goDiff` (`λ = 3/2`) on `(-1,1)`**: `C_c^∞((-1,1))` is a core for the
Friedrichs generator. -/
theorem go_esaProp : goDiff.ESAProp :=
  DiffusionTriple.esaProp_of_orth goDiff go_orth_zero

end MarkovTriple.BGL.Instances.GegenbauerOpen
