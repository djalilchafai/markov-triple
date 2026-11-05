import Mathlib
import MarkovTriple.Stochastic.R31U.Tri
import MarkovTriple.BGL.Theory.Interp.JensenGrad
import MarkovTriple.BGL.Theory.Interp.ExtBdd
import MarkovTriple.BGL.Theory.Interp.IbpBdd
import MarkovTriple.BGL.Theory.Interp.Setup

/-!
# Round 31 (U), part 2: the interpolation `Θ(r) = ∫ P_r h · (P_{t-r} f)²` (BGL, proof of the reverse Poincaré inequality)

For `f, h ∈ 𝒜₀`, a finite measure and `CD(0,∞)`: `Θ` is continuous on `ℝ` and, for `0 < s < t`,
`Θ'(s) = 2 ∫ P_s h · Γ(P_{t-s} f)`.  The derivative is computed with the product rule `hasDerivAt_int3` for `L²`-curves that are
bounded in `L^∞`, the orbit calculus `hasDerivAt_orb` of `Interp/Orbit.lean`, and the Green formula `ibp_bdd` applied to the bounded
elements `P_s h`, `(P_{t-s} f)²` (`Bdd`, finite measure).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Stochastic.R31U

open MarkovTriple.BGL MarkovTriple.BGL.FullTriple

variable {E : Type*} [MeasurableSpace E] (T : FullTriple E)

/-- uniform `L^∞` bound of the orbit of a test function -/
lemma orb_bound (ψ : T.A₀) : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, ∀ᵐ x ∂T.μ, |(T.orb ψ r : E → ℝ) x| ≤ C := by
  obtain ⟨C, hC⟩ := T.toDiffusionTriple.bounded ψ.1 ψ.2
  refine ⟨|C| + 1, by positivity, fun r => ?_⟩
  refine ae_abs_semigroup_le T.toDiffusionTriple (by positivity) (u := T.toDiffusionTriple.cls ψ) ?_ _
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple ψ] with x hx
  rw [hx]
  exact (hC x).trans (by linarith [le_abs_self C])

variable {T}

/-- `P_r f` (`r ≥ 0` real) is a bounded element of `𝒜` (finite measure, `CD(0,∞)`) -/
lemma Pt_bdd [IsFiniteMeasure T.μ] (hCD : T.CD 0 ∞) (f : T.A₀) (r : ℝ) : Bdd T (T.Pt r.toNNReal f) := by
  obtain ⟨K, hK0, hK⟩ := orb_bound T f
  obtain ⟨K', hK'0, hK'⟩ := orb_bound T (T.Lt f)
  set γ : T.A₀ := ⟨T.toDiffusionTriple.ΓA f.1 f.1, T.ΓA_self_mem_A₀ f.2⟩ with hγ
  obtain ⟨Cγ, hCγ⟩ := T.toDiffusionTriple.bounded γ.1 γ.2
  have hκ : 0 < |Cγ| + 1 := by positivity
  refine ⟨T.Pt_mem_A _ f, K, max (|Cγ| + 1) K', ?_, ?_, ?_⟩
  · filter_upwards [hK r, T.Pt_ae r.toNNReal f] with x h1 h2
    have : (T.orb f r : E → ℝ) x = T.Pt r.toNNReal f x := h2
    rwa [← this]
  · have hGB := T.gradient_bound_unconditional hCD (le_refl 0) f r.toNNReal
    have hP := DiffusionTriple.semigroup_le_const (D := T.toDiffusionTriple) r.toNNReal
      (T.toDiffusionTriple.cls γ) hκ (by
        filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple γ] with x hx
        rw [hx]; exact (hCγ x).trans (by linarith [le_abs_self Cγ]) |>.trans' (le_abs_self _))
    filter_upwards [hGB, hP] with x h1 h2
    simp only [mul_zero, zero_mul, Real.exp_zero, one_mul] at h1
    exact h1.trans (h2.trans (le_max_left _ _))
  · filter_upwards [T.L_Pt_ae f r, hK' r] with x h1 h2
    rw [h1]
    exact h2.trans (le_max_right _ _)

namespace Bdd'

variable [IsFiniteMeasure T.μ] {h : E → ℝ}

lemma memQ (hb : Bdd T h) : hb.memLp2.toLp h ∈ T.formDomain :=
  ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form hb.domain).1

lemma integrable_L (hb : Bdd T h) : Integrable (T.L h) T.μ := by
  obtain ⟨hA, -, B, -, -, hL⟩ := hb
  exact intB (T.A_measurable _ (L_memA hA)) hL

end Bdd'

/-- integrability of a product of three bounded `𝒜`-elements -/
lemma integrable_mul3 [IsFiniteMeasure T.μ] {u v w : E → ℝ} (hu : u ∈ T.A) (hv : v ∈ T.A) (hw : w ∈ T.A)
    {Cu Cv Cw : ℝ} (h1 : ∀ᵐ x ∂T.μ, |u x| ≤ Cu) (h2 : ∀ᵐ x ∂T.μ, |v x| ≤ Cv)
    (h3 : ∀ᵐ x ∂T.μ, |w x| ≤ Cw) : Integrable (fun x => u x * v x * w x) T.μ := by
  refine intB ((T.A_measurable u hu).mul (T.A_measurable v hv) |>.mul (T.A_measurable w hw))
    (C := Cu * Cv * Cw) ?_
  filter_upwards [h1, h2, h3] with x a b c
  rw [abs_mul, abs_mul]
  have h0 : 0 ≤ Cu := (abs_nonneg _).trans a
  have h0' : 0 ≤ Cv := (abs_nonneg _).trans b
  exact mul_le_mul (mul_le_mul a b (abs_nonneg _) h0) c (abs_nonneg _) (mul_nonneg h0 h0')

/-- Green: `∫ L k · g² = ∫ k · L(g²)` for bounded elements `k`, `g` -/
lemma ibp_sq [IsFiniteMeasure T.μ] {kk gg : E → ℝ} (hk : Bdd T kk) (hg : Bdd T gg) :
    ∫ x, T.L kk x * gg x ^ 2 ∂T.μ = ∫ x, kk x * T.L (fun y => gg y ^ 2) x ∂T.μ := by
  have hb2 : Bdd T (fun y => gg y ^ 2) := hg.comp (ψ := fun y : ℝ => y ^ 2) (contDiff_id.pow 2)
  obtain ⟨K2, -, hK2, -, -⟩ := hb2.2
  obtain ⟨K1, -, hK1, -, -⟩ := hk.2
  have i1 := ibp_bdd (T := T) (Gf := fun y => gg y ^ 2) hb2.memA hb2.memLp2 (Bdd'.memQ hb2)
    (Bdd'.integrable_L hb2) hk.memA hk.memLp2 (Bdd'.memQ hk) hK1
  have i2 := ibp_bdd (T := T) (Gf := kk) hk.memA hk.memLp2 (Bdd'.memQ hk) (Bdd'.integrable_L hk)
    hb2.memA hb2.memLp2 (Bdd'.memQ hb2) hK2
  have hc : T.toDiffusionTriple.ΓA (fun y => gg y ^ 2) kk = T.toDiffusionTriple.ΓA kk (fun y => gg y ^ 2) :=
    DiffusionTriple.ΓA_comm T.toDiffusionTriple _ _
  have e : ∫ x, G T (fun y => gg y ^ 2) kk x ∂T.μ = ∫ x, G T kk (fun y => gg y ^ 2) x ∂T.μ := by
    show ∫ x, T.toDiffusionTriple.ΓA (fun y => gg y ^ 2) kk x ∂T.μ =
      ∫ x, T.toDiffusionTriple.ΓA kk (fun y => gg y ^ 2) x ∂T.μ
    rw [hc]
  have := i1.2
  have := i2.2
  simp only [mul_comm (gg _ ^ 2)] at *
  linarith

variable (T) in
/-- the interpolation function `Θ(r) = ∫ P_r h · (P_{t-r} f)²` -/
noncomputable def theta (f h : T.A₀) (t : ℝ≥0) (r : ℝ) : ℝ :=
  ∫ x, (T.orb h r : E → ℝ) x * (T.orb f ((t : ℝ) - r) : E → ℝ) x * (T.orb f ((t : ℝ) - r) : E → ℝ) x ∂T.μ

lemma theta_continuous (f h : T.A₀) (t : ℝ≥0) : Continuous (theta T f h t) := by
  obtain ⟨Ch, -, hCh⟩ := orb_bound T h
  obtain ⟨Cf, -, hCf⟩ := orb_bound T f
  have hf : Continuous fun r : ℝ => T.orb f ((t : ℝ) - r) :=
    (T.continuous_orb f).comp (continuous_const.sub continuous_id)
  exact tri_continuous (a := fun r => T.orb h r) (b := fun r => T.orb f ((t : ℝ) - r))
    (c := fun r => T.orb f ((t : ℝ) - r)) (T.continuous_orb h) hf hf (M := max Ch Cf)
    (fun r => (hCh r).mono fun x hx => hx.trans (le_max_left _ _))
    (fun r => (hCf _).mono fun x hx => hx.trans (le_max_right _ _))

/-- **Derivative of the interpolation** (BGL, proof of the reverse Poincaré inequality):
`Θ'(s) = 2 ∫ P_s h · Γ(P_{t-s} f)` for `0 < s < t`. -/
theorem theta_hasDerivAt [IsFiniteMeasure T.μ] (hCD : T.CD 0 ∞) (f h : T.A₀) (t : ℝ≥0) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) :
    HasDerivAt (theta T f h t) (2 * ∫ x, T.Pt s.toNNReal h x *
      T.toDiffusionTriple.ΓA (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ) s := by
  obtain ⟨Ch, -, hCh⟩ := orb_bound T h
  obtain ⟨Cf, -, hCf⟩ := orb_bound T f
  have ha : HasDerivAt (fun r => T.orb h r) (T.orb (T.Lt h) s) s := T.hasDerivAt_orb h hs.1
  have hb : HasDerivAt (fun r : ℝ => T.orb f ((t : ℝ) - r)) (-(T.orb (T.Lt f) ((t : ℝ) - s))) s := by
    have := (T.hasDerivAt_orb f (sub_pos.2 hs.2)).scomp s ((hasDerivAt_id s).const_sub (t : ℝ))
    have h2 : HasDerivAt (fun r : ℝ => T.orb f ((t : ℝ) - r))
        ((-1 : ℝ) • T.orb (T.Lt f) ((t : ℝ) - s)) s := this
    simpa using h2
  have hD := hasDerivAt_int3 ha hb hb (M := max Ch Cf)
    (fun r => (hCh r).mono fun x hx => hx.trans (le_max_left _ _))
    (fun r => (hCf _).mono fun x hx => hx.trans (le_max_right _ _))
    (fun r => (hCf _).mono fun x hx => hx.trans (le_max_right _ _))
  convert hD using 1
  · rfl
  -- identification of the derivative
  set σ : ℝ≥0 := ((t : ℝ) - s).toNNReal with hσ
  set kk := T.Pt s.toNNReal h with hkk
  set gg := T.Pt σ f with hgg
  have hkB : Bdd T kk := Pt_bdd hCD h s
  have hgB : Bdd T gg := Pt_bdd hCD f ((t : ℝ) - s)
  have e_a : (T.orb h s : E → ℝ) =ᵐ[T.μ] kk := T.Pt_ae s.toNNReal h
  have e_g : (T.orb f ((t : ℝ) - s) : E → ℝ) =ᵐ[T.μ] gg := T.Pt_ae σ f
  have e_Lk : (T.orb (T.Lt h) s : E → ℝ) =ᵐ[T.μ] T.L kk := (T.L_Pt_ae h s).symm
  have e_Lg : (T.orb (T.Lt f) ((t : ℝ) - s) : E → ℝ) =ᵐ[T.μ] T.L gg := (T.L_Pt_ae f ((t : ℝ) - s)).symm
  have e_n : (-(T.orb (T.Lt f) ((t : ℝ) - s)) : Lp ℝ 2 T.μ) =ᵐ[T.μ] fun x => -(T.L gg x) := by
    filter_upwards [Lp.coeFn_neg (T.orb (T.Lt f) ((t : ℝ) - s)), e_Lg] with x h1 h2
    rw [h1]; simp only [Pi.neg_apply, h2]
  -- bounds
  obtain ⟨K1, B1, hK1, hΓ1, hL1⟩ := hkB.2
  obtain ⟨K2, B2, hK2, hΓ2, hL2⟩ := hgB.2
  have hLkA : T.L kk ∈ T.A := L_memA hkB.memA
  have hLgA : T.L gg ∈ T.A := L_memA hgB.memA
  have hΓA : G T gg gg ∈ T.A := G_mem hgB.memA hgB.memA
  have hΓ0 : 0 ≤ᵐ[T.μ] G T gg gg := T.ΓA_nonneg gg hgB.memA
  have hΓb : ∀ᵐ x ∂T.μ, |G T gg gg x| ≤ |B2| := by
    filter_upwards [hΓ2, hΓ0] with x h1 h2
    have : 0 ≤ G T gg gg x := h2
    rw [abs_of_nonneg this]; exact h1.trans (le_abs_self _)
  -- the three integrals
  have I1 : ∫ x, (T.orb (T.Lt h) s : E → ℝ) x * (T.orb f ((t : ℝ) - s) : E → ℝ) x *
      (T.orb f ((t : ℝ) - s) : E → ℝ) x ∂T.μ = ∫ x, T.L kk x * gg x ^ 2 ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [e_Lk, e_g] with x h1 h2
    rw [h1, h2]; ring
  have I2 : ∫ x, (T.orb h s : E → ℝ) x * (-(T.orb (T.Lt f) ((t : ℝ) - s)) : Lp ℝ 2 T.μ) x *
      (T.orb f ((t : ℝ) - s) : E → ℝ) x ∂T.μ = -∫ x, kk x * gg x * T.L gg x ∂T.μ := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [e_a, e_g, e_n] with x h1 h2 h3
    rw [h1, h2, h3]; ring
  have I3 : ∫ x, (T.orb h s : E → ℝ) x * (T.orb f ((t : ℝ) - s) : E → ℝ) x *
      (-(T.orb (T.Lt f) ((t : ℝ) - s)) : Lp ℝ 2 T.μ) x ∂T.μ = -∫ x, kk x * gg x * T.L gg x ∂T.μ := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [e_a, e_g, e_n] with x h1 h2 h3
    rw [h1, h2, h3]; ring
  have iA : Integrable (fun x => kk x * gg x * T.L gg x) T.μ :=
    integrable_mul3 hkB.memA hgB.memA hLgA hK1 hK2 hL2
  have iB : Integrable (fun x => kk x * G T gg gg x) T.μ := by
    refine intB ((T.A_measurable _ hkB.memA).mul (T.A_measurable _ hΓA)) (C := K1 * |B2|) ?_
    filter_upwards [hK1, hΓb] with x a b
    rw [abs_mul]
    exact mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
  have hL2sq : T.L (fun y => gg y ^ 2) =ᵐ[T.μ] fun x => 2 * (gg x * T.L gg x) + 2 * G T gg gg x := by
    have := L_comp T (ψ := fun y : ℝ => y ^ 2) (contDiff_id.pow 2) hgB.memA
    filter_upwards [this] with x hx
    rw [hx]
    have d1 : deriv (fun y : ℝ => y ^ 2) (gg x) = 2 * gg x := by simp
    have d2 : deriv (deriv (fun y : ℝ => y ^ 2)) (gg x) = 2 := by
      have : deriv (fun y : ℝ => y ^ 2) = fun y => 2 * y := by funext y; simp
      rw [this]; simp
    rw [d1, d2]; ring
  have I1' : ∫ x, T.L kk x * gg x ^ 2 ∂T.μ =
      2 * ∫ x, kk x * gg x * T.L gg x ∂T.μ + 2 * ∫ x, kk x * G T gg gg x ∂T.μ := by
    rw [ibp_sq hkB hgB]
    have : ∫ x, kk x * T.L (fun y => gg y ^ 2) x ∂T.μ =
        ∫ x, (2 * (kk x * gg x * T.L gg x) + 2 * (kk x * G T gg gg x)) ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hL2sq] with x hx
      rw [hx]; ring
    rw [this, integral_add (iA.const_mul 2) (iB.const_mul 2), integral_const_mul, integral_const_mul]
  have e_kk : ∫ x, kk x * T.toDiffusionTriple.ΓA gg gg x ∂T.μ = ∫ x, kk x * G T gg gg x ∂T.μ := rfl
  rw [e_kk] at *
  linarith [I1, I2, I3, I1']

end MarkovTriple.Stochastic.R31U
