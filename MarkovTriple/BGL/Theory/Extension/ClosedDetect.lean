import Mathlib
import MarkovTriple.BGL.Theory.Extension.ClosedIdent

/-!
# `𝒜₀` detects `L¹` functions

`ae_zero_of_forall_integral_A₀`: if `φ ∈ L¹(μ)` and `∫ k φ dμ = 0` for every `k ∈ 𝒜₀`, then `φ = 0` a.e.
(density of `𝒜₀` in `L²` (D2), stability of `𝒜₀` under the smooth cut-offs `ψ_m(t) = t e^{-t²/m}` (D2), the exhaustion
sequence (Def. 3.1.1) and dominated convergence).  It is the routine "density of `𝒜₀`" step used in the proofs of
BGL Props 3.3.5 (i) and 3.3.17 ("it is enough to check against every `k ∈ 𝒜₀`").
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- the smooth bounded cut-off `ψ_m(t) = t e^{-t²/m}`. -/
noncomputable def psiCut (m : ℕ) (t : ℝ) : ℝ := t * Real.exp (-(t ^ 2) / (m + 1))

lemma psiCut_zero (m : ℕ) : psiCut m 0 = 0 := by simp [psiCut]

lemma contDiff_psiCut (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => psiCut m (z 0)) := by
  unfold psiCut
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => z 0) := contDiff_apply ℝ ℝ 0
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => Real.exp (-(z 0 ^ 2) / ((m : ℝ) + 1))) := by
    refine Real.contDiff_exp.comp ?_
    exact ((h1.pow 2).neg).div_const _
  exact h1.mul h2

lemma abs_psiCut_le (m : ℕ) (t : ℝ) : |psiCut m t| ≤ |t| := by
  unfold psiCut
  rw [abs_mul]
  have : |Real.exp (-(t ^ 2) / ((m : ℝ) + 1))| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.2
    have : 0 ≤ t ^ 2 / ((m : ℝ) + 1) := by positivity
    rw [neg_div]; linarith
  nlinarith [abs_nonneg t, abs_nonneg (Real.exp (-(t ^ 2) / ((m : ℝ) + 1)))]

lemma abs_psiCut_le_const (m : ℕ) (t : ℝ) : |psiCut m t| ≤ (m : ℝ) + 1 := by
  by_cases ht : |t| ≤ 1
  · exact (abs_psiCut_le m t).trans (ht.trans (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]))
  · have ht : 1 < |t| := not_le.1 ht
    unfold psiCut
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    set M : ℝ := (m : ℝ) + 1 with hM
    have hM1 : 1 ≤ M := by rw [hM]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have h1 : t ^ 2 / M ≤ Real.exp (t ^ 2 / M) := by linarith [Real.add_one_le_exp (t ^ 2 / M)]
    have h2 : Real.exp (-(t ^ 2) / M) = (Real.exp (t ^ 2 / M))⁻¹ := by
      rw [← Real.exp_neg, neg_div]
    rw [h2]
    have ht0 : 0 < t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have ht2 : 0 < t ^ 2 / M := div_pos ht0 (by linarith)
    have hE : 0 < Real.exp (t ^ 2 / M) := Real.exp_pos _
    rw [← div_eq_mul_inv, div_le_iff₀ hE]
    have : |t| * 1 ≤ M * (t ^ 2 / M) := by
      have e : M * (t ^ 2 / M) = t ^ 2 := by field_simp
      rw [e, mul_one]
      have := abs_nonneg t
      nlinarith [sq_abs t]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ M)]

lemma tendsto_psiCut (t : ℝ) : Tendsto (fun m : ℕ => psiCut m t) atTop (𝓝 t) := by
  unfold psiCut
  have h : Tendsto (fun m : ℕ => -(t ^ 2) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := -(t ^ 2))).div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa using this
  have := (Real.continuous_exp.tendsto 0).comp h
  simpa using this.const_mul t

/-- **Step 1**: bounded measurable `L²` functions are annihilated against `φ`. -/
lemma integral_bdd_zero {φ : E → ℝ} (hφ : Integrable φ T.μ)
    (h : ∀ k : T.A₀, ∫ x, k.1 x * φ x ∂T.μ = 0) {q : E → ℝ} (hq : Measurable q) {B : ℝ}
    (hB : ∀ x, |q x| ≤ B) (hq2 : MemLp q 2 T.μ) : ∫ x, q x * φ x ∂T.μ = 0 := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  have hdense := T.dense 2 this (by simp)
  obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.1 (hdense (hq2.toLp q))
  have hs' : ∀ n, ∃ k : T.A₀, ((s n : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] k.1 := by
    intro n
    obtain ⟨f, hf, hae⟩ := hs n
    exact ⟨⟨f, hf⟩, hae⟩
  choose k hk using hs'
  obtain ⟨ν, hν, hae⟩ := Lp_ae_subseq hslim
  have hall : ∀ᵐ x ∂T.μ, ∀ n, ((s n : Lp ℝ 2 T.μ) : E → ℝ) x = (k n).1 x := ae_all_iff.2 hk
  have hqq := hq2.coeFn_toLp
  have hconv : ∀ᵐ x ∂T.μ, Tendsto (fun n => (k (ν n)).1 x) atTop (𝓝 (q x)) := by
    filter_upwards [hae, hall, hqq] with x h1 h2 h3
    rw [h3] at h1
    exact h1.congr (fun n => h2 (ν n))
  -- cut off
  have step : ∀ m : ℕ, ∫ x, psiCut m (q x) * φ x ∂T.μ = 0 := by
    intro m
    have hmem : ∀ n, (fun x => psiCut m ((k n).1 x)) ∈ T.A₀ := fun n =>
      T.comp_mem 1 (fun z => psiCut m (z 0)) (contDiff_psiCut m) (psiCut_zero m)
        (fun _ => (k n).1) (fun _ => (k n).2)
    have hz : ∀ n, ∫ x, psiCut m ((k n).1 x) * φ x ∂T.μ = 0 := fun n =>
      h ⟨_, hmem n⟩
    have hcont : Continuous (psiCut m) := by
      unfold psiCut; fun_prop
    have hD := tendsto_integral_of_dominated_convergence (μ := T.μ)
      (F := fun n x => psiCut m ((k (ν n)).1 x) * φ x)
      (f := fun x => psiCut m (q x) * φ x) (fun x => ((m : ℝ) + 1) * |φ x|)
      (fun n => by
        have hm : Measurable (fun x => psiCut m ((k (ν n)).1 x)) :=
          hcont.measurable.comp (T.measurable _ (k (ν n)).2)
        exact (hm.aestronglyMeasurable.mul hφ.aestronglyMeasurable))
      (hφ.abs.const_mul _)
      (fun n => Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_psiCut_le_const m _) (abs_nonneg _))
      (by
        filter_upwards [hconv] with x hx
        exact ((hcont.tendsto _).comp hx).mul_const _)
    have : Tendsto (fun n => ∫ x, psiCut m ((k (ν n)).1 x) * φ x ∂T.μ) atTop (𝓝 0) :=
      tendsto_const_nhds.congr (fun n => (hz (ν n)).symm)
    exact tendsto_nhds_unique hD this
  -- remove the cut-off
  have hD := tendsto_integral_of_dominated_convergence (μ := T.μ)
    (F := fun m x => psiCut m (q x) * φ x) (f := fun x => q x * φ x)
    (fun x => B * |φ x|)
    (fun m => by
      have hcont : Continuous (psiCut m) := by
        unfold psiCut; fun_prop
      exact ((hcont.measurable.comp hq).aestronglyMeasurable.mul hφ.aestronglyMeasurable))
    (hφ.abs.const_mul _)
    (fun m => Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((abs_psiCut_le m _).trans (hB x)) (abs_nonneg _))
    (Eventually.of_forall fun x => (tendsto_psiCut (q x)).mul_const _)
  have : Tendsto (fun m : ℕ => ∫ x, psiCut m (q x) * φ x ∂T.μ) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun m => (step m).symm)
  exact tendsto_nhds_unique hD this

/-- **`𝒜₀` detects `L¹`** : `φ ∈ L¹` with `∫ k φ = 0` for all `k ∈ 𝒜₀` vanishes a.e. -/
theorem ae_zero_of_forall_integral_A₀ {φ : E → ℝ} (hφ : Integrable φ T.μ)
    (h : ∀ k : T.A₀, ∫ x, k.1 x * φ x ∂T.μ = 0) : φ =ᵐ[T.μ] 0 := by
  -- measurable representative
  set φ0 : E → ℝ := hφ.aestronglyMeasurable.mk φ with hφ0
  have hm0 : Measurable φ0 := hφ.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : φ =ᵐ[T.μ] φ0 := hφ.aestronglyMeasurable.ae_eq_mk
  have hi0 : Integrable φ0 T.μ := hφ.congr he
  have h0 : ∀ k : T.A₀, ∫ x, k.1 x * φ0 x ∂T.μ = 0 := fun k => by
    rw [← h k]
    exact integral_congr_ae (by filter_upwards [he] with x hx; rw [hx])
  obtain ⟨u, hu1, _, hu3⟩ := T.exhaustion
  have hn : ∀ n, ∀ᵐ x ∂T.μ, |u n x| * |φ0 x| = 0 := by
    intro n
    obtain ⟨B, hB⟩ := T.bounded (u n) (hu1 n)
    set q : E → ℝ := fun x => |u n x| * (if 0 ≤ φ0 x then 1 else -1) with hq
    have hqm : Measurable q := by
      refine (T.measurable (u n) (hu1 n)).abs.mul ?_
      exact Measurable.ite (measurableSet_le measurable_const hm0) measurable_const measurable_const
    have hqB : ∀ x, |q x| ≤ |B| := by
      intro x
      simp only [hq, abs_mul]
      have : |(if 0 ≤ φ0 x then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
      rw [this, mul_one, abs_abs]
      exact (hB x).trans (le_abs_self B)
    have hq2 : MemLp q 2 T.μ := by
      have := (T.memLp (u n) (hu1 n) 2 (by norm_num) (by simp))
      refine this.mono hqm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      simp only [hq, Real.norm_eq_abs, abs_mul]
      have : |(if 0 ≤ φ0 x then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
      rw [this, mul_one, abs_abs]
    have hz := integral_bdd_zero hi0 h0 hqm hqB hq2
    have hqφ : ∀ x, q x * φ0 x = |u n x| * |φ0 x| := by
      intro x
      simp only [hq]
      split_ifs with hx
      · rw [abs_of_nonneg hx]; ring
      · have hx' := not_le.1 hx
        rw [abs_of_neg hx']; ring
    have hint : Integrable (fun x => |u n x| * |φ0 x|) T.μ := by
      refine (hi0.abs.const_mul (|B|)).mono' ((T.measurable (u n) (hu1 n)).abs.aestronglyMeasurable.mul
        hm0.abs.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
      exact mul_le_mul_of_nonneg_right ((hB x).trans (le_abs_self B)) (abs_nonneg _)
    have hz' : ∫ x, |u n x| * |φ0 x| ∂T.μ = 0 := by
      rw [← hz]; exact integral_congr_ae (Eventually.of_forall fun x => (hqφ x).symm)
    exact (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hint).1 hz'
  have hall := ae_all_iff.2 hn
  filter_upwards [he, hall, hu3] with x h1 h2 h3
  rw [h1]
  show φ0 x = 0
  have hev : ∀ᶠ n in atTop, (1 / 2 : ℝ) < |u n x| := by
    have := (continuous_abs.tendsto _).comp h3
    simp only [abs_one] at this
    exact this.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨n, hn'⟩ := hev.exists
  have := h2 n
  rcases mul_eq_zero.1 this with h | h
  · linarith [abs_nonneg (u n x)]
  · exact abs_eq_zero.1 h

/-- **BGL Prop. 3.3.5 (i)**: if `f ∈ 𝒜 ∩ L²` belongs to `𝒟(L*)` (the adjoint of `L|𝒜₀`, Def. 3.1.9), i.e. there is
`w ∈ L²` with `⟪f, L a⟫ = ⟪w, a⟫` for all `a ∈ 𝒜₀` (`L* f = w`), then `L* f = L f` (a.e.). -/
theorem adjoint_eq_L {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ) (w : Lp ℝ 2 T.μ)
    (hw : ∀ a : T.A₀, inner ℝ (hf2.toLp f) (T.toDiffusionTriple.Lcls a) =
      inner ℝ w (T.toDiffusionTriple.cls a)) :
    ((w : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] T.L f := by
  have hLf := L_memA (T := T) hf
  refine ae_eq_of_mul_A₀ (fun k => ?_)
  have hk2 := DiffusionTriple.memLp2 T.toDiffusionTriple k.2
  -- `k (w - L f)` is integrable
  have i1 : Integrable (fun x => k.1 x * (w : E → ℝ) x) T.μ := (hk2.integrable_mul (Lp.memLp w))
  have i2 : Integrable (fun x => k.1 x * T.L f x) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal _ hLf k.1 k.2)
  have hint : Integrable (fun x => k.1 x * ((w : E → ℝ) x - T.L f x)) T.μ := by
    refine (i1.sub i2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  have key : ∀ k' : T.A₀, ∫ x, k'.1 x * (k.1 x * ((w : E → ℝ) x - T.L f x)) ∂T.μ = 0 := by
    intro k'
    set m : T.A₀ := k' * k with hm
    have hmx : (m : E → ℝ) = fun x => k'.1 x * k.1 x := rfl
    have e1 : ∫ x, m.1 x * (w : E → ℝ) x ∂T.μ = ∫ x, f x * T.L m.1 x ∂T.μ := by
      have := hw m
      rw [L2_inner_eq, L2_inner_eq] at this
      have a1 : ∫ x, (hf2.toLp f : E → ℝ) x * (T.toDiffusionTriple.Lcls m : E → ℝ) x ∂T.μ =
          ∫ x, f x * T.L m.1 x ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple m] with x h1 h2
        rw [h1, h2]
      have a2 : ∫ x, (w : E → ℝ) x * (T.toDiffusionTriple.cls m : E → ℝ) x ∂T.μ =
          ∫ x, m.1 x * (w : E → ℝ) x ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple m] with x h2
        rw [h2]; ring
      rw [← a1, ← a2]; exact this.symm
    have e2 := T.ibp_A f hf m.1 m.2
    have e3 : ∫ x, m.1 x * T.L f x ∂T.μ = ∫ x, f x * T.L m.1 x ∂T.μ := by
      linarith [e2.1, e2.2]
    have hmw : Integrable (fun x => m.1 x * (w : E → ℝ) x) T.μ :=
      (DiffusionTriple.memLp2 T.toDiffusionTriple m.2).integrable_mul (Lp.memLp w)
    have hmL : Integrable (fun x => m.1 x * T.L f x) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal _ hLf m.1 m.2)
    have : (fun x => k'.1 x * (k.1 x * ((w : E → ℝ) x - T.L f x))) =
        fun x => m.1 x * (w : E → ℝ) x - m.1 x * T.L f x := by
      funext x; rw [hmx]; ring
    rw [this, integral_sub hmw hmL, e1, e3, sub_self]
  have hz := ae_zero_of_forall_integral_A₀ hint key
  filter_upwards [hz] with x hx
  simp only [Pi.zero_apply] at hx
  have : k.1 x * ((w : E → ℝ) x - T.L f x) = 0 := hx
  linarith

end FullTriple

end MarkovTriple.BGL
