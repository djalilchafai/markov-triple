import Mathlib
import MarkovTriple.Stochastic.R31U.Theta
import MarkovTriple.Stochastic.RieszRep
import MarkovTriple.BGL.Theory.Strong.Main
import MarkovTriple.BGL.Theory.Interp.StrongMain

/-!
# Round 31 (U), part 3: the reverse Poincaré inequality, sup-form (U1)

Route (BGL, proof of the reverse Poincaré inequality): for `f, h ∈ 𝒜₀`, `h ≥ 0`, `0 < s < t`:

* (monotonicity, Thm 3.3.18 for `ρ = 0`, `ε`-form) `∫ h ψ_ε(Γ(P_t f)) ≤ ∫ P_s h ψ_ε(Γ(P_{t-s} f))`;
* (`ψ_ε(r)² ≤ r` and AM-GM, `∫ P_s h ≤ ∫ h`) `B² ≤ (∫ h) · ∫ P_s h Γ(P_{t-s} f)`, `B = ∫ h ψ_ε(Γ(P_t f))`;
* (`Θ' = 2 ∫ P_s h Γ(P_{t-s} f)`, `theta_hasDerivAt`) hence `Θ(t) - Θ(0) ≥ 2 t B² / ∫ h`, `Θ(t) ≤ C² ∫ h`, `Θ(0) ≥ 0`;
* positivity detection F2 turns `B ≤ (C/√(2t)) ∫ h` into `ψ_ε(Γ(P_t f)) ≤ C/√(2t)` a.e., and `ε → 0`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Stochastic.R31U

open MarkovTriple.BGL MarkovTriple.BGL.FullTriple

variable {E : Type*} [MeasurableSpace E] {T : FullTriple E}

lemma psiS_nonneg' {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) : 0 ≤ psiS ε r := by
  rw [psiS_eq hε (by nlinarith [sq_pos_of_pos hε])]
  have : ε ≤ Real.sqrt (r + ε ^ 2) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  linarith

lemma psiS_sq_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) : psiS ε r ^ 2 ≤ r := by
  have h1 := psiS_nonneg' hε hr
  have h2 := psiS_le_sqrt hε hr
  calc psiS ε r ^ 2 ≤ Real.sqrt r ^ 2 := by gcongr
    _ = r := Real.sq_sqrt hr

/-- **Monotonicity of the `ε`-interpolation** (Thm 3.3.18, `ρ = 0`): `Φ_ε(0) ≤ Φ_ε(s)` for `0 ≤ s ≤ t`. -/
theorem strong_mono {n : ℝ≥0∞} (hCD : T.CD 0 n) {ε : ℝ} (hε : 0 < ε) (f h : T.A₀)
    (hh : 0 ≤ᵐ[T.μ] h.1) (t : ℝ≥0) : MonotoneOn (T.strongPhi ε f h t) (Icc 0 (t : ℝ)) := by
  have hS := T.strongInterpolation hCD
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hS.continuousOn ε hε f h hh t) ?_ ?_
  · rw [interior_Icc]
    intro s hs
    exact (hS.hasDerivAt ε hε f h hh t s hs).2.2.differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro s hs
    obtain ⟨-, -, hd⟩ := hS.hasDerivAt ε hε f h hh t s hs
    rw [hd.deriv]
    have hk0 : 0 ≤ᵐ[T.μ] T.Pt s.toNNReal h := T.Pt_nonneg _ h hh
    have hge := strongD_ge T hCD (le_refl 0) hε (T.Pt_mem_A ((t : ℝ) - s).toNNReal f)
    refine integral_nonneg_of_ae ?_
    filter_upwards [hk0, hge] with x h1 h2
    exact mul_nonneg h1 (by simpa using h2)

section Endpoints

variable [IsFiniteMeasure T.μ]

omit [IsFiniteMeasure T.μ] in
lemma cls_nonneg (h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) :
    0 ≤ᵐ[T.μ] (T.toDiffusionTriple.cls h : E → ℝ) := by
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple h, hh] with x h1 h2
  rw [h1]; exact h2

/-- mass is non-increasing: `∫ P_s h ≤ ∫ h` for `h ≥ 0` -/
lemma integral_orb_le (h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) (r : ℝ) :
    ∫ x, (T.orb h r : E → ℝ) x ∂T.μ ≤ ∫ x, h.1 x ∂T.μ := by
  have := Stochastic.integral_semigroup_le T.toDiffusionTriple r.toNNReal (T.toDiffusionTriple.cls h)
    (cls_nonneg h hh)
  refine this.trans (le_of_eq ?_)
  exact integral_congr_ae (DiffusionTriple.coeFn_cls T.toDiffusionTriple h)

omit [IsFiniteMeasure T.μ] in
lemma orb_nonneg (h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) (r : ℝ) : 0 ≤ᵐ[T.μ] (T.orb h r : E → ℝ) :=
  T.toDiffusionTriple.semigroup_nonneg _ (cls_nonneg h hh)

omit [IsFiniteMeasure T.μ] in
lemma theta_zero_nonneg (f h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) (t : ℝ≥0) : 0 ≤ theta T f h t 0 := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [orb_nonneg h hh 0] with x hx
  simp only [Pi.zero_apply]
  have : (T.orb h 0 : E → ℝ) x * (T.orb f ((t : ℝ) - 0) : E → ℝ) x * (T.orb f ((t : ℝ) - 0) : E → ℝ) x =
      (T.orb h 0 : E → ℝ) x * ((T.orb f ((t : ℝ) - 0) : E → ℝ) x) ^ 2 := by ring
  rw [this]
  exact mul_nonneg hx (sq_nonneg _)

lemma theta_t_le (f h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) {C : ℝ} (hC : ∀ᵐ x ∂T.μ, |f.1 x| ≤ C) (t : ℝ≥0) :
    theta T f h t t ≤ C ^ 2 * ∫ x, h.1 x ∂T.μ := by
  obtain ⟨Cf, -, hCf⟩ := orb_bound T f
  have hf0 : (T.orb f ((t : ℝ) - t) : E → ℝ) =ᵐ[T.μ] f.1 := by
    rw [sub_self, T.orb_zero f]
    exact DiffusionTriple.coeFn_cls T.toDiffusionTriple f
  have iL : Integrable (fun x => (T.orb h t : E → ℝ) x * (T.orb f ((t : ℝ) - t) : E → ℝ) x *
      (T.orb f ((t : ℝ) - t) : E → ℝ) x) T.μ := int3_integrable _ _ _ (hCf _)
  have ik : Integrable (fun x => (T.orb h t : E → ℝ) x) T.μ :=
    (Lp.memLp (T.orb h t)).integrable (by norm_num)
  have hle : theta T f h t t ≤ ∫ x, C ^ 2 * (T.orb h t : E → ℝ) x ∂T.μ := by
    refine integral_mono_ae iL (ik.const_mul _) ?_
    filter_upwards [orb_nonneg h hh t, hf0, hC] with x h1 h2 h3
    rw [h2]
    have : f.1 x ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    nlinarith [mul_le_mul_of_nonneg_left this h1]
  refine hle.trans ?_
  rw [integral_const_mul]
  have := integral_orb_le h hh t
  have e : (t : ℝ).toNNReal = t := Real.toNNReal_coe
  nlinarith [sq_nonneg C]

/-- the weak (integrated) form of the reverse Poincaré inequality, `ε`-regularised -/
theorem reverse_aux (hCD : T.CD 0 ∞) {ε : ℝ} (hε : 0 < ε) (f h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) {C : ℝ}
    (hC : ∀ᵐ x ∂T.μ, |f.1 x| ≤ C) (t : ℝ≥0) (ht : 0 < t) :
    2 * (t : ℝ) * (∫ x, h.1 x * psiS ε (G T (T.Pt t f) (T.Pt t f) x) ∂T.μ) ^ 2 ≤
      C ^ 2 * (∫ x, h.1 x ∂T.μ) ^ 2 := by
  have hB : T.strongPhi ε f h t 0 = ∫ x, h.1 x * psiS ε (G T (T.Pt t f) (T.Pt t f) x) ∂T.μ := by
    unfold FullTriple.strongPhi
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_zero h] with x hx
    simp only [Real.toNNReal_zero, sub_zero, Real.toNNReal_coe, hx]
  set B := ∫ x, h.1 x * psiS ε (G T (T.Pt t f) (T.Pt t f) x) ∂T.μ with hBdef
  set H := ∫ x, h.1 x ∂T.μ with hHdef
  have hH0 : 0 ≤ H := integral_nonneg_of_ae hh
  have hΓ0 : 0 ≤ᵐ[T.μ] G T (T.Pt t f) (T.Pt t f) := T.ΓA_nonneg _ (T.Pt_mem_A t f)
  have hB0 : 0 ≤ B := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hh, hΓ0] with x h1 h2
    exact mul_nonneg h1 (psiS_nonneg' hε h2)
  rcases eq_or_lt_of_le hH0 with hH | hH
  · -- `h = 0` a.e.
    have hi : Integrable h.1 T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple h.2
    have h0 : h.1 =ᵐ[T.μ] 0 := by
      have := (integral_eq_zero_iff_of_nonneg_ae hh hi).1 hH.symm
      exact this
    have : B = 0 := by
      rw [hBdef]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [h0] with x h1
      simp only [h1, Pi.zero_apply, zero_mul]
    rw [this, ← hH]; simp
  -- `H > 0`
  have hkey : ∀ s ∈ Ioo (0 : ℝ) (t : ℝ), B ^ 2 ≤ H * ∫ x, T.Pt s.toNNReal h x *
      T.toDiffusionTriple.ΓA (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ := by
    intro s hs
    set kk := T.Pt s.toNNReal h with hkk
    set gg := T.Pt ((t : ℝ) - s).toNNReal f with hgg
    have hkB : Bdd T kk := Pt_bdd hCD h s
    have hgB : Bdd T gg := Pt_bdd hCD f ((t : ℝ) - s)
    have hk0 : 0 ≤ᵐ[T.μ] kk := T.Pt_nonneg _ h hh
    obtain ⟨K1, -, hK1, -, -⟩ := hkB.2
    obtain ⟨K2, B2, hK2, hΓ2, hL2⟩ := hgB.2
    have hΓA : G T gg gg ∈ T.A := G_mem hgB.memA hgB.memA
    have hΓg0 : 0 ≤ᵐ[T.μ] G T gg gg := T.ΓA_nonneg gg hgB.memA
    have hΓb : ∀ᵐ x ∂T.μ, |G T gg gg x| ≤ |B2| := by
      filter_upwards [hΓ2, hΓg0] with x h1 h2
      have : 0 ≤ G T gg gg x := h2
      rw [abs_of_nonneg this]; exact h1.trans (le_abs_self _)
    have iB : Integrable (fun x => kk x * G T gg gg x) T.μ := by
      refine intB ((T.A_measurable _ hkB.memA).mul (T.A_measurable _ hΓA)) (C := K1 * |B2|) ?_
      filter_upwards [hK1, hΓb] with x a b
      rw [abs_mul]
      exact mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
    have ik : Integrable kk T.μ := intB (T.A_measurable _ hkB.memA) hK1
    have hJ0 : 0 ≤ ∫ x, kk x * G T gg gg x ∂T.μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hk0, hΓg0] with x h1 h2
      exact mul_nonneg h1 h2
    set J := ∫ x, kk x * G T gg gg x ∂T.μ with hJ
    have hmono : B ≤ T.strongPhi ε f h t s := by
      rw [← hB]
      exact strong_mono hCD hε f h hh t ⟨le_rfl, t.2⟩ ⟨hs.1.le, hs.2.le⟩ hs.1.le
    have hm : ∫ x, kk x ∂T.μ ≤ H := by
      have := integral_orb_le h hh s
      refine le_trans (le_of_eq ?_) this
      exact (integral_congr_ae (T.Pt_ae s.toNNReal h)).symm
    obtain ⟨i1, -, -⟩ := (T.strongInterpolation hCD).hasDerivAt ε hε f h hh t s hs
    show B ^ 2 ≤ H * J
    rcases eq_or_lt_of_le hB0 with hB' | hB'
    · rw [← hB']; simpa using mul_nonneg hH0 hJ0
    set lam := B / H with hlam
    have hlam0 : 0 < lam := by positivity
    have hpt : ∀ᵐ x ∂T.μ, kk x * psiS ε (G T gg gg x) ≤ (lam * kk x + lam⁻¹ * (kk x * G T gg gg x)) / 2 := by
      filter_upwards [hk0, hΓg0] with x h1 h2
      have p0 := psiS_nonneg' hε h2
      have p1 := psiS_sq_le hε h2
      have : psiS ε (G T gg gg x) ≤ (lam + lam⁻¹ * G T gg gg x) / 2 := by
        have h3 : 2 * lam * psiS ε (G T gg gg x) ≤ lam ^ 2 + psiS ε (G T gg gg x) ^ 2 := by
          nlinarith [sq_nonneg (psiS ε (G T gg gg x) - lam)]
        have h4 : psiS ε (G T gg gg x) ≤ (lam ^ 2 + G T gg gg x) / (2 * lam) := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
        refine h4.trans (le_of_eq ?_)
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left this h1]
    have hint : ∫ x, kk x * psiS ε (G T gg gg x) ∂T.μ ≤
        ∫ x, (lam * kk x + lam⁻¹ * (kk x * G T gg gg x)) / 2 ∂T.μ :=
      integral_mono_ae i1 (((ik.const_mul _).add (iB.const_mul _)).div_const 2) hpt
    have hrhs : ∫ x, (lam * kk x + lam⁻¹ * (kk x * G T gg gg x)) / 2 ∂T.μ =
        (lam * ∫ x, kk x ∂T.μ + lam⁻¹ * J) / 2 := by
      rw [integral_div, integral_add (ik.const_mul _) (iB.const_mul _), integral_const_mul,
        integral_const_mul]
    have hphi : T.strongPhi ε f h t s = ∫ x, kk x * psiS ε (G T gg gg x) ∂T.μ := rfl
    have h5 : B ≤ (lam * H + lam⁻¹ * J) / 2 := by
      have := hmono.trans (hphi ▸ hint)
      rw [hrhs] at this
      have := mul_le_mul_of_nonneg_left hm hlam0.le
      linarith
    have h6 : lam * H = B := by rw [hlam]; field_simp
    have h7 : lam⁻¹ * J = H * J / B := by rw [hlam]; field_simp
    rw [h6, h7] at h5
    have : B * B ≤ H * J := by
      have : 2 * B ≤ B + H * J / B := by linarith
      have h8 : B ≤ H * J / B := by linarith
      rwa [le_div_iff₀ hB'] at h8
    nlinarith
  -- integration of the derivative
  set c : ℝ := 2 * (B ^ 2 / H) with hc
  have hmonoΘ : MonotoneOn (fun r => theta T f h t r - c * r) (Icc 0 (t : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact ((theta_continuous f h t).sub (continuous_const.mul continuous_id)).continuousOn
    · rw [interior_Icc]
      intro s hs
      have hd : HasDerivAt (fun r => theta T f h t r - c * r) (2 * ∫ x, T.Pt s.toNNReal h x *
          T.toDiffusionTriple.ΓA (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ
          - c) s := by
        have hd0 := (theta_hasDerivAt hCD f h t hs).sub ((hasDerivAt_id s).const_mul c)
        simp only [id, mul_one] at hd0
        exact hd0
      exact hd.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      have hd : HasDerivAt (fun r => theta T f h t r - c * r) (2 * ∫ x, T.Pt s.toNNReal h x *
          T.toDiffusionTriple.ΓA (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ
          - c) s := by
        have hd0 := (theta_hasDerivAt hCD f h t hs).sub ((hasDerivAt_id s).const_mul c)
        simp only [id, mul_one] at hd0
        exact hd0
      rw [hd.deriv]
      have := hkey s hs
      have h9 : B ^ 2 / H ≤ ∫ x, T.Pt s.toNNReal h x *
          T.toDiffusionTriple.ΓA (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ := by
        rw [div_le_iff₀ hH]; linarith
      rw [hc]; linarith
  have h10 := hmonoΘ (a := 0) (b := (t : ℝ)) ⟨le_rfl, t.2⟩ ⟨t.2, le_rfl⟩ t.2
  simp only [mul_zero, sub_zero] at h10
  have h11 := theta_zero_nonneg f h hh t
  have h12 := theta_t_le f h hh hC t
  have h13 : c * t ≤ C ^ 2 * H := by linarith
  rw [hc] at h13
  have h14 : 2 * (B ^ 2 / H) * t * H = 2 * t * B ^ 2 := by field_simp
  have h15 := mul_le_mul_of_nonneg_right h13 hH.le
  nlinarith [h14, h15]

/-- **U1: sup-form of the reverse Poincaré inequality** (BGL; finite measure, `CD(0,∞)`). -/
theorem reverse_poincare_sup' (hCD : T.CD 0 ∞) (f : T.A₀) {C : ℝ} (hC : ∀ᵐ x ∂T.μ, |f.1 x| ≤ C)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ x ∂T.μ, 2 * (t : ℝ) * T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) x ≤ C ^ 2 := by
  have hC' : ∀ᵐ x ∂T.μ, |f.1 x| ≤ |C| := hC.mono fun x hx => hx.trans (le_abs_self _)
  have ht2 : 0 < 2 * (t : ℝ) := by positivity
  set c : ℝ := |C| / Real.sqrt (2 * (t : ℝ)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : c ^ 2 * (2 * (t : ℝ)) = C ^ 2 := by
    rw [hc, div_pow, Real.sq_sqrt ht2.le, sq_abs]; field_simp
  have hΓA : G T (T.Pt t f) (T.Pt t f) ∈ T.A := G_mem (T.Pt_mem_A t f) (T.Pt_mem_A t f)
  have hΓ0 : 0 ≤ᵐ[T.μ] G T (T.Pt t f) (T.Pt t f) := T.ΓA_nonneg _ (T.Pt_mem_A t f)
  have hε : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hpsi : ∀ n : ℕ, ∀ᵐ x ∂T.μ, psiS (1 / ((n : ℝ) + 1)) (G T (T.Pt t f) (T.Pt t f) x) ≤ c := by
    intro n
    set ε := 1 / ((n : ℝ) + 1) with hεdef
    have hu : (fun x => c - psiS ε (G T (T.Pt t f) (T.Pt t f) x)) ∈ T.A :=
      T.A.sub_mem (T.const_mem_A c) (T.comp_mem_A (psiS_smooth (hε n)) hΓA)
    have := T.pos_detect _ hu (fun h hh h0 => by
      set h' : T.A₀ := ⟨h, hh⟩
      have hr := reverse_aux hCD (hε n) f h' h0 hC' t ht
      set B := ∫ x, h x * psiS ε (G T (T.Pt t f) (T.Pt t f) x) ∂T.μ with hB
      set H := ∫ x, h x ∂T.μ with hH
      have hH0 : 0 ≤ H := integral_nonneg_of_ae h0
      have hB0 : 0 ≤ B := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [h0, hΓ0] with x h1 h2
        exact mul_nonneg h1 (psiS_nonneg' (hε n) h2)
      have hBc : B ≤ c * H := by
        by_contra hlt
        push Not at hlt
        have h1 : (c * H) ^ 2 < B ^ 2 := by nlinarith [mul_nonneg hc0 hH0]
        have h2 : 2 * (t : ℝ) * B ^ 2 ≤ |C| ^ 2 * H ^ 2 := hr
        have h3 : 2 * (t : ℝ) * (c * H) ^ 2 = |C| ^ 2 * H ^ 2 := by
          have : c ^ 2 * (2 * (t : ℝ)) = |C| ^ 2 := by rw [hc2, sq_abs]
          nlinarith [this]
        nlinarith
      have e : ∫ x, h x * (c - psiS ε (G T (T.Pt t f) (T.Pt t f) x)) ∂T.μ = c * H - B := by
        have i1 : Integrable h T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple hh
        have i2 : Integrable (fun x => h x * psiS ε (G T (T.Pt t f) (T.Pt t f) x)) T.μ :=
          DiffusionTriple.integrable_of_mem T.toDiffusionTriple
            (T.ideal _ (T.comp_mem_A (psiS_smooth (hε n)) hΓA) h hh)
        have : (fun x => h x * (c - psiS ε (G T (T.Pt t f) (T.Pt t f) x))) =
            fun x => c * h x - h x * psiS ε (G T (T.Pt t f) (T.Pt t f) x) := by
          funext x; ring
        rw [this, integral_sub (i1.const_mul c) i2, integral_const_mul]
      rw [e]; linarith)
    filter_upwards [this] with x hx
    simpa using hx
  have hall : ∀ᵐ x ∂T.μ, ∀ n : ℕ, psiS (1 / ((n : ℝ) + 1)) (G T (T.Pt t f) (T.Pt t f) x) ≤ c :=
    ae_all_iff.2 hpsi
  filter_upwards [hall, hΓ0] with x h1 h2
  have h3 : Real.sqrt (G T (T.Pt t f) (T.Pt t f) x) ≤ c :=
    le_of_tendsto' (tendsto_psiS_sqrt h2) h1
  have h4 : G T (T.Pt t f) (T.Pt t f) x ≤ c ^ 2 := by
    calc G T (T.Pt t f) (T.Pt t f) x = Real.sqrt (G T (T.Pt t f) (T.Pt t f) x) ^ 2 :=
          (Real.sq_sqrt h2).symm
      _ ≤ c ^ 2 := by gcongr
  show 2 * (t : ℝ) * G T (T.Pt t f) (T.Pt t f) x ≤ C ^ 2
  nlinarith [mul_le_mul_of_nonneg_left h4 ht2.le]

end Endpoints

section Main

variable (T : FullTriple E) [IsFiniteMeasure T.μ]

/-- **U1** (frozen statement): sup-form of the reverse Poincaré inequality. -/
theorem reverse_poincare_sup (hCD : T.CD 0 ∞) (f : T.A₀) {C : ℝ} (hC : ∀ᵐ x ∂T.μ, |f.1 x| ≤ C)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ x ∂T.μ, 2 * (t : ℝ) * T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) x ≤ C ^ 2 :=
  reverse_poincare_sup' hCD f hC t ht

end Main

end MarkovTriple.Stochastic.R31U
