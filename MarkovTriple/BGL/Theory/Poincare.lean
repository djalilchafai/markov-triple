import Mathlib
import MarkovTriple.FunctionalInequalities.GapFromSquare
import MarkovTriple.BGL.Theory.Gamma2Integral
import MarkovTriple.BGL.Theory.ESAOne
import MarkovTriple.BGL.Frozen.Poincare
import MarkovTriple.BGL.Calculus.Density
import MarkovTriple.Hilbert.SpectralGap

/-!
# Poincaré inequality from `CD(ρ,n)` (BGL Prop. 4.8.3, Thm 4.8.4, Lichnerowicz)

Book route (integrated `L²` / spectral):

1. `ρ ℰ(f) + n⁻¹ ‖L f‖² ≤ ‖L f‖²` on `𝒜₀` (`Theory/Gamma2Integral.lean`), extended to `𝒟(L)` by ESA.
2. With `R = (1 + B)⁻¹` the resolvent of the Friedrichs generator (`B = -L`), this is
   `ρ ⟪w - R w, R w⟫ ≤ ‖w - R w‖²` for all `w` (`square_all`; the set of `w` of the form
   `(1 - L)a`, `a ∈ 𝒜₀`, is dense by ESA).
3. The abstract Hilbert lemma `Hilbert.gap_of_square` (continuous functional calculus of `R`).
4. Ergodicity S10 identifies `ker(1 - R)` with the constants; the centred function `g - ∫ g`
   equals `R w` with `w ⟂ 1` (`1 ∈ 𝒟(L)`, `L 1 = 0` is itself derived from ESA, `ESAOne.lean`).

Main results (`T : FullTriple`, `μ` a probability measure):
* `poincare_of_CD_infty`: `CD(ρ,∞)`, `ρ > 0` ⇒ `T.PI (1/ρ)` (book, Cor. 4.8.2 / Prop. 4.8.3);
* `poincare_of_CD_dim`: `CD(ρ,n)`, `1 < n`, `ρ > 0` ⇒ `T.PI ((1 - n⁻¹)/ρ) = PI((n-1)/(ρ n))`
  (Thm 4.8.4; Lichnerowicz: spectral gap `ρ n/(n-1)`);
* `poincare_extend_domain`: the inequality on all of `𝒟(ℰ)` (`DiffusionTriple.PI.extend`).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace DiffusionTriple

variable (T : DiffusionTriple E)

/-- ESA ⇒ the vectors `[a] - [L a]`, `a ∈ 𝒜₀`, are dense in `L²` (range criterion). -/
lemma mem_closure_range_one_sub_L (hesa : T.ESAProp) (w : Lp ℝ 2 T.μ) :
    w ∈ closure {y : Lp ℝ 2 T.μ | ∃ a : T.A₀, y = T.cls a - T.Lcls a} := by
  set S := formData T
  obtain ⟨h, hG⟩ := S.generator_R w
  have hG' : (T.generator ⟨S.R w, h⟩ : Lp ℝ 2 T.μ) = S.R w - w := hG
  obtain ⟨a, ha1, ha2⟩ := hesa (S.R w) h
  rw [hG'] at ha2
  have hlim : Tendsto (fun k => T.cls (a k) - T.Lcls (a k)) atTop (𝓝 (S.R w - (S.R w - w))) :=
    ha1.sub ha2
  rw [show S.R w - (S.R w - w) = w by abel] at hlim
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ⟨a k, rfl⟩)

/-- **The squared inequality for every vector** (`ρ ⟪w - R w, R w⟫ ≤ ‖w - R w‖²`). -/
theorem square_all (hesa : T.ESAProp) {ρ : ℝ}
    (hρ : ∀ a : T.A₀, ρ * (-inner ℝ (T.Lcls a) (T.cls a)) ≤ ‖T.Lcls a‖ ^ 2) (w : Lp ℝ 2 T.μ) :
    ρ * inner ℝ (w - (formData T).R w) ((formData T).R w) ≤ ‖w - (formData T).R w‖ ^ 2 := by
  set S := formData T
  have hC : IsClosed {w : Lp ℝ 2 T.μ | ρ * inner ℝ (w - S.R w) (S.R w) ≤ ‖w - S.R w‖ ^ 2} := by
    apply isClosed_le <;> fun_prop
  have hsub : {y : Lp ℝ 2 T.μ | ∃ a : T.A₀, y = T.cls a - T.Lcls a} ⊆
      {w : Lp ℝ 2 T.μ | ρ * inner ℝ (w - S.R w) (S.R w) ≤ ‖w - S.R w‖ ^ 2} := by
    rintro y ⟨a, rfl⟩
    have hR : S.R (T.cls a - T.Lcls a) = T.cls a := R_cls_sub T a
    show ρ * inner ℝ (T.cls a - T.Lcls a - S.R (T.cls a - T.Lcls a)) (S.R (T.cls a - T.Lcls a)) ≤
      ‖T.cls a - T.Lcls a - S.R (T.cls a - T.Lcls a)‖ ^ 2
    rw [hR, show T.cls a - T.Lcls a - T.cls a = -T.Lcls a by abel, inner_neg_left, norm_neg]
    exact hρ a
  exact closure_minimal hsub hC (mem_closure_range_one_sub_L T hesa w)

/-- Under S10, the fixed space of the resolvent consists of constants. -/
theorem fixed_const (herg : ∀ (u : Lp ℝ 2 T.μ) (hu : u ∈ T.generator.domain),
      T.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : E → ℝ) =ᵐ[T.μ] fun _ => c)
    (n : Lp ℝ 2 T.μ) (hn : (formData T).R n = n) :
    ∃ c : ℝ, (n : E → ℝ) =ᵐ[T.μ] fun _ => c := by
  set S := formData T
  have hdom : n ∈ S.generator.domain := (S.mem_domain_generator_iff n).2 ⟨0, by simpa using hn⟩
  have hG : S.generator ⟨n, hdom⟩ = 0 := (S.generator_apply_eq_iff hdom 0).2 (by simpa using hn)
  exact herg n hdom hG

variable [IsProbabilityMeasure T.μ]

lemma inner_cls_one2 (a : T.A₀) : inner ℝ (T.cls a) T.one2 = ∫ x, a.1 x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cls T a, T.coeFn_one2] with x h1 h2
  rw [h1, h2, mul_one]

lemma inner_one2_one2 : inner ℝ T.one2 T.one2 = 1 := by
  rw [L2_inner_eq]
  have : ∫ x, (T.one2 : E → ℝ) x * (T.one2 : E → ℝ) x ∂T.μ = ∫ _x, (1 : ℝ) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [T.coeFn_one2] with x h2
    rw [h2, mul_one]
  rw [this]; simp

/-- **`ρ Var(g) ≤ ℰ(g)` on test functions**, from the integrated squared inequality, ESA, S10. -/
theorem rho_var_le_of (hesa : T.ESAProp)
    (herg : ∀ (u : Lp ℝ 2 T.μ) (hu : u ∈ T.generator.domain),
      T.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : E → ℝ) =ᵐ[T.μ] fun _ => c)
    {ρ : ℝ} (hρ : ∀ a : T.A₀, ρ * (-inner ℝ (T.Lcls a) (T.cls a)) ≤ ‖T.Lcls a‖ ^ 2)
    {g : E → ℝ} (hg : g ∈ T.A₀) :
    ρ * ProbabilityTheory.variance g T.μ ≤ ∫ x, T.Γ g g x ∂T.μ := by
  set S := formData T with hS
  set m : ℝ := ∫ x, g x ∂T.μ with hm
  set a : T.A₀ := ⟨g, hg⟩ with ha
  set u : Lp ℝ 2 T.μ := T.cls a - m • T.one2 with hu
  set w : Lp ℝ 2 T.μ := T.cls a - T.Lcls a - m • T.one2 with hw
  have hRw : S.R w = u := by
    have h1 := R_cls_sub T a
    have h2 := R_one2 T hesa
    show S.R (T.cls a - T.Lcls a - m • T.one2) = T.cls a - m • T.one2
    rw [map_sub, map_smul, h1, h2]
  have hLone : inner ℝ (T.Lcls a) T.one2 = 0 := inner_Lcls_one2 T a
  have horth : ∀ v : Lp ℝ 2 T.μ, S.R v = v → inner ℝ w v = 0 := by
    intro v hv
    obtain ⟨c, hc⟩ := fixed_const T herg v hv
    have hvc : v = c • T.one2 := by
      refine Lp.ext ?_
      filter_upwards [hc, T.coeFn_one2, Lp.coeFn_smul c T.one2] with x h1 h2 h3
      rw [h1, h3, Pi.smul_apply, h2]; simp
    rw [hvc, inner_smul_right, hw, inner_sub_left, inner_sub_left, inner_smul_left,
      inner_cls_one2, hLone, inner_one2_one2]
    simp [hm, ha]
  have hgap := Hilbert.gap_of_square (R := S.R) S.R_unitOp ρ (square_all T hesa hρ) horth
  rw [hRw] at hgap
  have hwu : w - u = -T.Lcls a := by rw [hw, hu]; abel
  rw [hwu, inner_neg_left, hu, inner_sub_right, inner_smul_right, hLone, inner_Lcls_cls] at hgap
  have hn : ‖u‖ ^ 2 = ∫ x, (g x - m) * (g x - m) ∂T.μ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_cls T a, T.coeFn_one2, Lp.coeFn_sub (T.cls a) (m • T.one2),
      Lp.coeFn_smul m T.one2] with x h1 h2 h3 h4
    have : (u : E → ℝ) x = g x - m := by
      rw [hu, h3, Pi.sub_apply, h1, h4, Pi.smul_apply, h2]; simp [ha]
    rw [this]
  have hg2 : MemLp g 2 T.μ := T.memLp g hg 2 (by norm_num) (by simp)
  have hvar : ProbabilityTheory.variance g T.μ = ∫ x, (g x - m) * (g x - m) ∂T.μ := by
    rw [ProbabilityTheory.variance_eq_integral hg2.aestronglyMeasurable.aemeasurable]
    simp only [← sq]
    rfl
  rw [hvar, ← hn]
  have e : (-∫ x, T.Γ a.1 (a.1) x ∂T.μ) = -∫ x, T.Γ g g x ∂T.μ := rfl
  simp only [mul_zero, sub_zero] at hgap
  linarith [hgap]

end DiffusionTriple

namespace FullTriple

variable (T : FullTriple E) [IsProbabilityMeasure T.μ]

/-- **Poincaré inequality from `CD(ρ,∞)`** (BGL Prop. 4.8.3 / Cor. 4.8.2): `ρ > 0`, probability
measure ⇒ `PI(1/ρ)` on `𝒜₀` (`Var f ≤ ρ⁻¹ ∫ Γ(f)`). -/
theorem poincare_of_CD_infty {ρ : ℝ} (hρ : 0 < ρ) (hCD : T.CD ρ ∞) :
    T.toDiffusionTriple.PI (1 / ρ) := by
  refine ⟨inferInstance, by positivity, fun f hf => ?_⟩
  have h := DiffusionTriple.rho_var_le_of T.toDiffusionTriple T.esaProp T.ergodic
    (fun a => by simpa using CD_integrated_cls T hCD a) hf
  show ProbabilityTheory.variance f T.μ ≤ 1 / ρ * ∫ x, T.Γ f f x ∂T.μ
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hρ]
  linarith

/-- **Lichnerowicz / BGL Thm 4.8.4**: `CD(ρ,n)`, `1 < n ≤ ∞`, `ρ > 0` ⇒ `PI((1 - n⁻¹)/ρ)`, i.e.
`PI((n-1)/(ρ n))` (`n = ∞`: `PI(1/ρ)`); the spectral gap is `≥ ρ n/(n-1)`. -/
theorem poincare_of_CD_dim {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ) (hn : 1 < n) (hCD : T.CD ρ n) :
    T.toDiffusionTriple.PI ((1 - (n⁻¹).toReal) / ρ) := by
  have hc : (n⁻¹).toReal < 1 := by
    have h1 : n⁻¹ < 1 := ENNReal.inv_lt_one.2 hn
    have h2 : n⁻¹ ≠ ∞ := ne_top_of_lt h1
    have := (ENNReal.toReal_lt_toReal h2 ENNReal.one_ne_top).2 h1
    simpa using this
  set c : ℝ := (n⁻¹).toReal with hcdef
  have hc1 : 0 < 1 - c := by linarith
  refine ⟨inferInstance, by positivity, fun f hf => ?_⟩
  have h := DiffusionTriple.rho_var_le_of T.toDiffusionTriple T.esaProp T.ergodic
    (ρ := ρ / (1 - c)) (fun a => by
      have h0 := CD_integrated_cls T hCD a
      rw [div_mul_eq_mul_div, div_le_iff₀ hc1]
      nlinarith [h0]) hf
  show ProbabilityTheory.variance f T.μ ≤ (1 - c) / ρ * ∫ x, T.Γ f f x ∂T.μ
  have hρ' : 0 < ρ / (1 - c) := by positivity
  have key : (1 - c) / ρ = (ρ / (1 - c))⁻¹ := by rw [inv_div]
  rw [key, inv_mul_eq_div, le_div_iff₀ hρ']
  linarith

/-- The Poincaré inequality of `poincare_of_CD_infty` on the whole Dirichlet domain. -/
theorem poincare_extend_domain {ρ : ℝ} (hρ : 0 < ρ) (hCD : T.CD ρ ∞) (u : T.toDiffusionTriple.formDomain) :
    ProbabilityTheory.variance ((u : Lp ℝ 2 T.μ) : E → ℝ) T.μ ≤
      1 / ρ * T.toDiffusionTriple.closedForm u u :=
  DiffusionTriple.PI.extend T.toDiffusionTriple (poincare_of_CD_infty T hρ hCD) u

end FullTriple

namespace DiffusionTriple

variable (T : DiffusionTriple E) [IsProbabilityMeasure T.μ]

/-- **Poincaré ⇒ spectral gap** (Hilbert form): `PI(C)` gives `λ ‖u‖² ≤ ℰ(u)` with `λ = 1/C` for
every `u ∈ 𝒟(ℰ)` orthogonal to the fixed space of the resolvent (the constants). -/
theorem hasSpectralGap_of_PI (hesa : T.ESAProp) {C : ℝ} (hPI : T.PI C) :
    (formData T).HasSpectralGap (1 / C) := by
  intro u hu
  have hC : 0 < C := hPI.2.1
  have hfix := hu T.one2 (R_one2 T hesa)
  have hmean : ∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ∂T.μ = 0 := by
    have : inner ℝ (u : Lp ℝ 2 T.μ) T.one2 = ∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ∂T.μ := by
      rw [L2_inner_eq]
      refine integral_congr_ae ?_
      filter_upwards [T.coeFn_one2] with x h2
      rw [h2, mul_one]
    rw [← this]; exact hfix
  have hext := PI.extend T hPI (u : T.formDomain)
  have hvar : ProbabilityTheory.variance ((u : Lp ℝ 2 T.μ) : E → ℝ) T.μ =
      ‖(u : Lp ℝ 2 T.μ)‖ ^ 2 := by
    rw [ProbabilityTheory.variance_eq_integral (Lp.memLp _ |>.aestronglyMeasurable.aemeasurable),
      hmean, ← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sq]
  rw [hvar] at hext
  show 1 / C * ‖(u : Lp ℝ 2 T.μ)‖ ^ 2 ≤ T.closedForm u u
  rw [one_div, inv_mul_le_iff₀ hC]
  exact hext

/-- **`L²` exponential decay** `‖P_t u‖ ≤ e^{-t/C} ‖u‖` for `u ⟂ 1`, from `PI(C)`. -/
theorem expDecay_of_PI (hesa : T.ESAProp) {C : ℝ} (hPI : T.PI C) :
    (formData T).HasExpDecay (1 / C) :=
  (formData T).hasExpDecay_of_hasSpectralGap (by have := hPI.2.1; positivity)
    (hasSpectralGap_of_PI T hesa hPI)

end DiffusionTriple

namespace FullTriple

variable (T : FullTriple E) [IsProbabilityMeasure T.μ]

/-- **Spectral gap from `CD(ρ,n)`** (Lichnerowicz): `λ = ρ n/(n-1)`, i.e. `1/C` with
`C = (1 - n⁻¹)/ρ`; for `n = ∞`, `λ = ρ`. -/
theorem hasSpectralGap_of_CD_dim {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ) (hn : 1 < n) (hCD : T.CD ρ n) :
    (DiffusionTriple.formData T.toDiffusionTriple).HasSpectralGap (1 / ((1 - (n⁻¹).toReal) / ρ)) :=
  DiffusionTriple.hasSpectralGap_of_PI T.toDiffusionTriple T.esaProp
    (poincare_of_CD_dim T hρ hn hCD)

end FullTriple

end MarkovTriple.BGL
