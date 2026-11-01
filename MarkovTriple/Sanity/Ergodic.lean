import Mathlib
import MarkovTriple.Frozen.Ergodic
import MarkovTriple.Frozen.Energy
import MarkovTriple.Sanity.Circle
import MarkovTriple.Audit.TwoPoint

/-! # Ergodicity: relation between the two forms, the `Bool` non-example, the circle statement
(NOT frozen). -/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

private lemma integrable_of_mem (T : MarkovTriple E) {f : E → ℝ} (hf : f ∈ T.A₀) :
    Integrable f T.μ :=
  memLp_one_iff_integrable.1 (T.memLp f hf 1 (by simp))

private lemma energy_nonneg (T : MarkovTriple E) {f : E → ℝ} (hf : f ∈ T.A₀) :
    0 ≤ T.energy f :=
  integral_nonneg fun x => T.Γ_nonneg f hf x

private lemma Γ_quad (T : MarkovTriple E) {f g : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀) (t : ℝ) :
    T.Γ (f + t • g) (f + t • g) = T.Γ f f + (2 * t) • T.Γ f g + (t ^ 2) • T.Γ g g := by
  have htg : t • g ∈ T.A₀ := T.A₀.smul_mem hg t
  have hfg : f + t • g ∈ T.A₀ := T.A₀.add_mem hf htg
  have e1 : T.Γ (f + t • g) (f + t • g) = T.Γ f (f + t • g) + t • T.Γ g (f + t • g) := by
    rw [T.Γ_add f hf (t • g) htg _ hfg, T.Γ_smul t g hg _ hfg]
  have e2 : T.Γ f (f + t • g) = T.Γ f f + t • T.Γ g f := by
    rw [T.Γ_symm f hf _ hfg, T.Γ_add f hf (t • g) htg f hf, T.Γ_smul t g hg f hf]
  have e3 : T.Γ g (f + t • g) = T.Γ f g + t • T.Γ g g := by
    rw [T.Γ_symm g hg _ hfg, T.Γ_add f hf (t • g) htg g hg, T.Γ_smul t g hg g hg]
  rw [e1, e2, e3, T.Γ_symm g hg f hf]
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma cross_zero (T : MarkovTriple E) {f g : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀)
    (h0 : T.energy f = 0) : ∫ x, T.Γ f g x ∂T.μ = 0 := by
  have iff_ := integrable_of_mem T (T.Γ_mem f hf f hf)
  have ifg := integrable_of_mem T (T.Γ_mem f hf g hg)
  have igg := integrable_of_mem T (T.Γ_mem g hg g hg)
  have key : ∀ t : ℝ, 0 ≤ 2 * t * ∫ x, T.Γ f g x ∂T.μ + t ^ 2 * T.energy g := by
    intro t
    have hn := energy_nonneg T (T.A₀.add_mem hf (T.A₀.smul_mem hg t))
    have : T.energy (f + t • g) = T.energy f + 2 * t * ∫ x, T.Γ f g x ∂T.μ + t ^ 2 * T.energy g := by
      unfold energy
      rw [Γ_quad T hf hg t]
      have : (fun x => (T.Γ f f + (2 * t) • T.Γ f g + (t ^ 2) • T.Γ g g) x) =
          fun x => T.Γ f f x + (2 * t) * T.Γ f g x + t ^ 2 * T.Γ g g x := by
        ext x; simp
      simp only [this]
      have i1 : Integrable (fun x => T.Γ f f x) T.μ := iff_
      have i2 : Integrable (fun x => 2 * t * T.Γ f g x) T.μ := ifg.const_mul (2 * t)
      have i3 : Integrable (fun x => t ^ 2 * T.Γ g g x) T.μ := igg.const_mul (t ^ 2)
      have i12 : Integrable (fun x => T.Γ f f x + 2 * t * T.Γ f g x) T.μ := i1.add i2
      rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul]
    rw [this, h0] at hn
    linarith
  by_contra hX
  set X := ∫ x, T.Γ f g x ∂T.μ
  set G := T.energy g
  have hG := energy_nonneg T hg
  have hk := key (-X / (G + 1))
  have hG1 : 0 < G + 1 := by linarith
  have hX2 : 0 < X ^ 2 := by positivity
  have hq : 2 * (-X / (G + 1)) * X + (-X / (G + 1)) ^ 2 * G = -(X ^ 2 * (G + 2)) / (G + 1) ^ 2 := by
    field_simp; ring
  have hneg : -(X ^ 2 * (G + 2)) / (G + 1) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · have : 0 < X ^ 2 * (G + 2) := by positivity
      linarith
    · positivity
  rw [hq] at hk
  linarith

/-- The L²-closure form of ergodicity implies the elementary Γ form. -/
theorem ErgodicL2.toErgodicΓ {T : MarkovTriple E} (h : T.ErgodicL2) : T.ErgodicΓ := by
  intro f hf hΓ
  have h0 : T.energy f = 0 := by
    unfold energy; exact integral_eq_zero_of_ae hΓ
  have hL : T.L f =ᵐ[T.μ] 0 := by
    have hLf := T.L_mem f hf
    have h1 : ∫ x, T.L f x * T.L f x ∂T.μ = 0 := by
      have := T.ibp f hf (T.L f) hLf
      rw [this, cross_zero T hf hLf h0, neg_zero]
    have hint : Integrable (fun x => T.L f x * T.L f x) T.μ :=
      integrable_of_mem T (T.A₀.mul_mem hLf hLf)
    have := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _) hint).1 h1
    filter_upwards [this] with x hx
    simpa using hx
  have hmem : MemLp f 2 T.μ := T.memLp f hf 2 (by norm_num)
  have key : ∃ f' : ℕ → E → ℝ, (∀ n, f' n ∈ T.A₀) ∧
      Tendsto (fun n => eLpNorm (f' n - (hmem.toLp f : E → ℝ)) 2 T.μ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (T.L (f' n)) 2 T.μ) atTop (𝓝 0) := by
    have h1 : ∀ n : ℕ, eLpNorm ((fun _ : ℕ => f) n - (hmem.toLp f : E → ℝ)) 2 T.μ = 0 := by
      intro n
      rw [eLpNorm_congr_ae (g := 0)]
      · simp
      · filter_upwards [MemLp.coeFn_toLp hmem] with x hx
        simp [hx]
    have h2 : ∀ n : ℕ, eLpNorm (T.L ((fun _ : ℕ => f) n)) 2 T.μ = 0 := by
      intro n
      rw [eLpNorm_congr_ae (g := 0) hL]
      simp
    refine ⟨fun _ => f, fun _ => hf, ?_, ?_⟩
    · exact Tendsto.congr (fun n => (h1 n).symm) tendsto_const_nhds
    · exact Tendsto.congr (fun n => (h2 n).symm) tendsto_const_nhds
  obtain ⟨c, hc⟩ := h (hmem.toLp f) key
  exact ⟨c, (MemLp.coeFn_toLp hmem).symm.trans hc⟩

end MarkovTriple

namespace MarkovTriple.Audit

private lemma bool_ae_const {f : Bool → ℝ} {c : ℝ} (h : f =ᵐ[μ2] fun _ => c) : ∀ b, f b = c := by
  intro b
  by_contra hb
  have h1 := (ae_iff.1 h)
  have : μ2 {b} ≠ 0 := by
    unfold μ2
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
    simp [PMF.uniformOfFintype_apply]
  exact this (measure_mono_null (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hb) h1)

/-- The two-point trivial triple (`L = Γ = 0`) is **not** ergodic (Γ form). -/
theorem T2_not_ErgodicΓ : ¬ T2.toMarkovTriple.ErgodicΓ := by
  intro h
  obtain ⟨c, hc⟩ := h (fun b => if b then 1 else 0) Algebra.mem_top
    (by filter_upwards with x; simp [T2, Sanity.trivialFull, Sanity.trivialTriple])
  have h1 := bool_ae_const hc true
  have h2 := bool_ae_const hc false
  simp at h1 h2
  linarith

/-- ... nor in the L²-closure form. -/
theorem T2_not_ErgodicL2 : ¬ T2.toMarkovTriple.ErgodicL2 :=
  fun h => T2_not_ErgodicΓ h.toErgodicΓ

end MarkovTriple.Audit

namespace MarkovTriple.Sanity.Circle

/-- STATEMENT ONLY (not proved): the circle triple `ℝ/ℤ` with trig-polynomial test algebra is
ergodic in both senses. Kept as a `Prop`-valued definition so it carries no `sorry`. -/
def circle_ergodic_statement : Prop := circleTriple.ErgodicΓ ∧ circleTriple.ErgodicL2

end MarkovTriple.Sanity.Circle
