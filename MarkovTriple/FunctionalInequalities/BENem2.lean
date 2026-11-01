import Mathlib
import MarkovTriple.FunctionalInequalities.BENem

/-! # Bakry–Émery (Phase 4b): differentiating `r ↦ ∫ Λ(a_r) · b_r` -/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal
open MarkovTriple.Hilbert (oneL2)

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

lemma integrable_phi_mul_mul {φ : E → ℝ} (hφm : AEStronglyMeasurable φ μ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) (u v : Lp ℝ 2 μ) :
    Integrable (fun x => φ x * ((u : E → ℝ) x * (v : E → ℝ) x)) μ :=
  ((Lp.memLp u).integrable_mul (Lp.memLp v)).bdd_mul (c := C) hφm
    (Filter.Eventually.of_forall fun x => by simpa using hC x)

theorem hasDerivAt_int_comp_mul {Λ : ℝ → ℝ} (hΛ : ContDiff ℝ (⊤ : ℕ∞) Λ) {K₀ K₁ K₂ M : ℝ}
    (h0 : ∀ x, |Λ x| ≤ K₀) (h1 : ∀ x, |deriv Λ x| ≤ K₁)
    (h2 : ∀ x, |deriv (deriv Λ) x| ≤ K₂) (hM : 0 ≤ M)
    {a b : ℝ → Lp ℝ 2 μ} {a' b' : Lp ℝ 2 μ} {s : ℝ} (ha : HasDerivAt a a' s)
    (hb : HasDerivAt b b' s)
    (hMb : ∀ᶠ r in 𝓝 s, ∀ᵐ x ∂μ, |(b r : E → ℝ) x| ≤ M) :
    HasDerivAt (fun r => ∫ x, Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x ∂μ)
      ((∫ x, deriv Λ ((a s : E → ℝ) x) * ((a' : E → ℝ) x * (b s : E → ℝ) x) ∂μ) +
        ∫ x, Λ ((a s : E → ℝ) x) * (b' : E → ℝ) x ∂μ) s := by
  have hK₀ : 0 ≤ K₀ := (abs_nonneg _).trans (h0 0)
  have hK₁ : 0 ≤ K₁ := (abs_nonneg _).trans (h1 0)
  have hK₂ : 0 ≤ K₂ := (abs_nonneg _).trans (h2 0)
  have hΛc : Continuous Λ := hΛ.continuous
  have hΛ'c : Continuous (deriv Λ) := (contDiff_deriv_top hΛ).continuous
  have hmΛ : ∀ v : Lp ℝ 2 μ, AEStronglyMeasurable (fun x => Λ ((v : E → ℝ) x)) μ :=
    fun v => hΛc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)
  have hmΛ' : ∀ v : Lp ℝ 2 μ, AEStronglyMeasurable (fun x => deriv Λ ((v : E → ℝ) x)) μ :=
    fun v => hΛ'c.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)
  rw [hasDerivAt_iff_isLittleO]
  set c₀ : ℝ := ‖oneL2 μ‖ with hc₀
  have hd : (fun r => a r - a s - (r - s) • a') =o[𝓝 s] fun r => r - s :=
    hasDerivAt_iff_isLittleO.1 ha
  have he : (fun r => b r - b s - (r - s) • b') =o[𝓝 s] fun r => r - s :=
    hasDerivAt_iff_isLittleO.1 hb
  have hbig : (fun r => a r - a s) =O[𝓝 s] fun r => r - s := ha.isBigO_sub
  have hbc : ContinuousAt b s := hb.continuousAt
  have hpc : Tendsto (fun r => ‖b r - b s‖) (𝓝 s) (𝓝 0) := by
    have := ((hbc.sub (continuousAt_const (y := b s))).norm).tendsto
    simpa using this
  have hBev : ∀ᶠ r in 𝓝 s, ‖b r‖ ≤ ‖b s‖ + 1 := by
    have : ∀ᶠ r in 𝓝 s, ‖b r - b s‖ < 1 := hpc.eventually (gt_mem_nhds one_pos)
    filter_upwards [this] with r hr
    have := norm_le_norm_add_norm_sub' (b r) (b s)
    linarith [norm_sub_rev (b r) (b s)]
  set D : ℝ := (∫ x, deriv Λ ((a s : E → ℝ) x) * ((a' : E → ℝ) x * (b s : E → ℝ) x) ∂μ) +
    ∫ x, Λ ((a s : E → ℝ) x) * (b' : E → ℝ) x ∂μ with hD
  have key : ∀ r : ℝ, (∀ᵐ x ∂μ, |(b r : E → ℝ) x| ≤ M) → ‖b r‖ ≤ ‖b s‖ + 1 →
      ‖(∫ x, Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x ∂μ) -
        (∫ x, Λ ((a s : E → ℝ) x) * (b s : E → ℝ) x ∂μ) - (r - s) • D‖ ≤
      K₀ * c₀ * ‖b r - b s - (r - s) • b'‖ + K₁ * (‖b s‖ + 1) * ‖a r - a s - (r - s) • a'‖ +
        |r - s| * (K₁ * ‖a'‖ * ‖b r - b s‖) + M * K₂ * ‖a r - a s‖ ^ 2 := by
    intro r hMr hBr
    set u : Lp ℝ 2 μ := a r - a s with hu
    set d : Lp ℝ 2 μ := a r - a s - (r - s) • a' with hd'
    set p : Lp ℝ 2 μ := b r - b s with hp
    set e : Lp ℝ 2 μ := b r - b s - (r - s) • b' with he'
    have hu' : (u : E → ℝ) =ᵐ[μ] fun x => (a r : E → ℝ) x - (a s : E → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (a r) (a s)] with x hx
      rw [hu, hx]; rfl
    have hp' : (p : E → ℝ) =ᵐ[μ] fun x => (b r : E → ℝ) x - (b s : E → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (b r) (b s)] with x hx
      rw [hp, hx]; rfl
    have hd'' : (d : E → ℝ) =ᵐ[μ] fun x =>
        (a r : E → ℝ) x - (a s : E → ℝ) x - (r - s) * (a' : E → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (a r - a s) ((r - s) • a'), Lp.coeFn_sub (a r) (a s),
        Lp.coeFn_smul (r - s) a'] with x h1 h2 h3
      rw [hd', h1]
      simp only [Pi.sub_apply] at h2 ⊢
      rw [h2, h3]; simp
    have he'' : (e : E → ℝ) =ᵐ[μ] fun x =>
        (b r : E → ℝ) x - (b s : E → ℝ) x - (r - s) * (b' : E → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (b r - b s) ((r - s) • b'), Lp.coeFn_sub (b r) (b s),
        Lp.coeFn_smul (r - s) b'] with x h1 h2 h3
      rw [he', h1]
      simp only [Pi.sub_apply] at h2 ⊢
      rw [h2, h3]; simp
    -- the four pieces
    set ρ : E → ℝ := fun x => Λ ((a r : E → ℝ) x) - Λ ((a s : E → ℝ) x) -
      deriv Λ ((a s : E → ℝ) x) * ((a r : E → ℝ) x - (a s : E → ℝ) x) with hρ
    have hρb : ∀ᵐ x ∂μ, ‖ρ x * (b r : E → ℝ) x‖ ≤ M * K₂ * ((u : E → ℝ) x) ^ 2 := by
      filter_upwards [hu', hMr] with x hx hbx
      rw [Real.norm_eq_abs, abs_mul]
      have h3 : |ρ x| ≤ K₂ * ((u : E → ℝ) x) ^ 2 := by
        have := taylor2 hΛ h2 ((a s : E → ℝ) x) ((a r : E → ℝ) x)
        rw [hx]; simpa [hρ] using this
      calc |ρ x| * |(b r : E → ℝ) x| ≤ (K₂ * ((u : E → ℝ) x) ^ 2) * M :=
            mul_le_mul h3 hbx (abs_nonneg _) (by positivity)
        _ = M * K₂ * ((u : E → ℝ) x) ^ 2 := by ring
    have iP4 : Integrable (fun x => ρ x * (b r : E → ℝ) x) μ :=
      Integrable.mono' ((integrable_sq_L2 u).const_mul (M * K₂))
        (((hmΛ (a r)).sub (hmΛ (a s))).sub
          ((hmΛ' (a s)).mul ((Lp.aestronglyMeasurable (a r)).sub (Lp.aestronglyMeasurable (a s)))) |>.mul
          (Lp.aestronglyMeasurable (b r))) hρb
    have iP1 : Integrable (fun x => Λ ((a s : E → ℝ) x) * (e : E → ℝ) x) μ :=
      integrable_deriv_mul hΛc h0 (a s) e
    have iP2 : Integrable (fun x => deriv Λ ((a s : E → ℝ) x) *
        ((d : E → ℝ) x * (b r : E → ℝ) x)) μ :=
      integrable_phi_mul_mul (hmΛ' (a s)) (fun x => h1 _) d (b r)
    have iP3 : Integrable (fun x => deriv Λ ((a s : E → ℝ) x) *
        ((a' : E → ℝ) x * (p : E → ℝ) x)) μ :=
      integrable_phi_mul_mul (hmΛ' (a s)) (fun x => h1 _) a' p
    have iQ1 : Integrable (fun x => Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x) μ :=
      integrable_deriv_mul hΛc h0 (a r) (b r)
    have iQ2 : Integrable (fun x => Λ ((a s : E → ℝ) x) * (b s : E → ℝ) x) μ :=
      integrable_deriv_mul hΛc h0 (a s) (b s)
    have iD1 : Integrable (fun x => deriv Λ ((a s : E → ℝ) x) *
        ((a' : E → ℝ) x * (b s : E → ℝ) x)) μ :=
      integrable_phi_mul_mul (hmΛ' (a s)) (fun x => h1 _) a' (b s)
    have iD2 : Integrable (fun x => Λ ((a s : E → ℝ) x) * (b' : E → ℝ) x) μ :=
      integrable_deriv_mul hΛc h0 (a s) b'
    have eq1 : (∫ x, Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x ∂μ) -
        (∫ x, Λ ((a s : E → ℝ) x) * (b s : E → ℝ) x ∂μ) - (r - s) • D =
        (∫ x, Λ ((a s : E → ℝ) x) * (e : E → ℝ) x ∂μ) +
        (∫ x, deriv Λ ((a s : E → ℝ) x) * ((d : E → ℝ) x * (b r : E → ℝ) x) ∂μ) +
        ((r - s) * ∫ x, deriv Λ ((a s : E → ℝ) x) * ((a' : E → ℝ) x * (p : E → ℝ) x) ∂μ) +
        ∫ x, ρ x * (b r : E → ℝ) x ∂μ := by
      have eA : (∫ x, Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x ∂μ) -
          (∫ x, Λ ((a s : E → ℝ) x) * (b s : E → ℝ) x ∂μ) - (r - s) • D =
          ∫ x, (Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x - Λ ((a s : E → ℝ) x) * (b s : E → ℝ) x -
            (r - s) * (deriv Λ ((a s : E → ℝ) x) * ((a' : E → ℝ) x * (b s : E → ℝ) x) +
              Λ ((a s : E → ℝ) x) * (b' : E → ℝ) x)) ∂μ := by
        have i1 : Integrable (fun x => Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x -
            Λ ((a s : E → ℝ) x) * (b s : E → ℝ) x) μ := iQ1.sub iQ2
        have i2 : Integrable (fun x => (r - s) * (deriv Λ ((a s : E → ℝ) x) *
            ((a' : E → ℝ) x * (b s : E → ℝ) x) + Λ ((a s : E → ℝ) x) * (b' : E → ℝ) x)) μ :=
          (iD1.add iD2).const_mul _
        rw [integral_sub i1 i2, integral_sub iQ1 iQ2, integral_const_mul, integral_add iD1 iD2,
          smul_eq_mul, hD]
      have iS12 : Integrable (fun x => Λ ((a s : E → ℝ) x) * (e : E → ℝ) x +
          deriv Λ ((a s : E → ℝ) x) * ((d : E → ℝ) x * (b r : E → ℝ) x)) μ := iP1.add iP2
      have iP3' : Integrable (fun x => (r - s) * (deriv Λ ((a s : E → ℝ) x) *
          ((a' : E → ℝ) x * (p : E → ℝ) x))) μ := iP3.const_mul _
      have iS123 : Integrable (fun x => Λ ((a s : E → ℝ) x) * (e : E → ℝ) x +
          deriv Λ ((a s : E → ℝ) x) * ((d : E → ℝ) x * (b r : E → ℝ) x) +
          (r - s) * (deriv Λ ((a s : E → ℝ) x) * ((a' : E → ℝ) x * (p : E → ℝ) x))) μ :=
        iS12.add iP3'
      have hsum : ∫ x, (Λ ((a s : E → ℝ) x) * (e : E → ℝ) x +
          deriv Λ ((a s : E → ℝ) x) * ((d : E → ℝ) x * (b r : E → ℝ) x) +
          (r - s) * (deriv Λ ((a s : E → ℝ) x) * ((a' : E → ℝ) x * (p : E → ℝ) x)) +
          ρ x * (b r : E → ℝ) x) ∂μ =
          (∫ x, Λ ((a s : E → ℝ) x) * (e : E → ℝ) x ∂μ) +
          (∫ x, deriv Λ ((a s : E → ℝ) x) * ((d : E → ℝ) x * (b r : E → ℝ) x) ∂μ) +
          ((r - s) * ∫ x, deriv Λ ((a s : E → ℝ) x) * ((a' : E → ℝ) x * (p : E → ℝ) x) ∂μ) +
          ∫ x, ρ x * (b r : E → ℝ) x ∂μ := by
        rw [integral_add iS123 iP4, integral_add iS12 iP3', integral_add iP1 iP2,
          integral_const_mul]
      rw [eA, ← hsum]
      refine integral_congr_ae ?_
      filter_upwards [hu', hp', hd'', he''] with x h1 h2 h3 h4
      rw [h3, h4, h2]; simp only [hρ]; ring
    rw [eq1]
    have t1 : ‖∫ x, Λ ((a s : E → ℝ) x) * (e : E → ℝ) x ∂μ‖ ≤ K₀ * c₀ * ‖e‖ := by
      have := abs_int_two_le (φ := fun x => Λ ((a s : E → ℝ) x)) hK₀
        (Filter.Eventually.of_forall fun x => h0 _) e
      rw [Real.norm_eq_abs]
      calc _ ≤ K₀ * (‖e‖ * c₀) := this
        _ = _ := by ring
    have t2 : ‖∫ x, deriv Λ ((a s : E → ℝ) x) * ((d : E → ℝ) x * (b r : E → ℝ) x) ∂μ‖ ≤
        K₁ * (‖b s‖ + 1) * ‖d‖ := by
      have := abs_int_three_le (φ := fun x => deriv Λ ((a s : E → ℝ) x)) hK₁
        (Filter.Eventually.of_forall fun x => h1 _) d (b r)
      rw [Real.norm_eq_abs]
      calc _ ≤ K₁ * (‖d‖ * ‖b r‖) := this
        _ ≤ K₁ * (‖d‖ * (‖b s‖ + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBr (norm_nonneg _)) hK₁
        _ = _ := by ring
    have t3 : ‖(r - s) * ∫ x, deriv Λ ((a s : E → ℝ) x) * ((a' : E → ℝ) x * (p : E → ℝ) x) ∂μ‖ ≤
        |r - s| * (K₁ * ‖a'‖ * ‖p‖) := by
      have := abs_int_three_le (φ := fun x => deriv Λ ((a s : E → ℝ) x)) hK₁
        (Filter.Eventually.of_forall fun x => h1 _) a' p
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc _ ≤ K₁ * (‖a'‖ * ‖p‖) := this
        _ = _ := by ring
    have t4 : ‖∫ x, ρ x * (b r : E → ℝ) x ∂μ‖ ≤ M * K₂ * ‖u‖ ^ 2 := by
      refine (norm_integral_le_of_norm_le ((integrable_sq_L2 u).const_mul (M * K₂)) hρb).trans ?_
      rw [integral_const_mul, int_sq_L2]
    have hsplit : ∀ a b c d : ℝ, ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
      intro a b c d
      have h1 := norm_add_le (a + b + c) d
      have h2 := norm_add_le (a + b) c
      have h3 := norm_add_le a b
      linarith
    refine (hsplit _ _ _ _).trans ?_
    linarith [t1, t2, t3, t4]
  -- asymptotics
  have h2o : (fun r => ‖a r - a s‖ ^ 2) =o[𝓝 s] fun r => r - s := by
    have := (hbig.norm_left.pow 2)
    exact this.trans_isLittleO (sq_isLittleO_sub s)
  have hdo : (fun r => ‖a r - a s - (r - s) • a'‖) =o[𝓝 s] fun r => r - s := hd.norm_left
  have heo : (fun r => ‖b r - b s - (r - s) • b'‖) =o[𝓝 s] fun r => r - s := he.norm_left
  have hpo : (fun r => ‖b r - b s‖) =o[𝓝 s] fun _ => (1 : ℝ) := (isLittleO_one_iff ℝ).2 hpc
  have h3o : (fun r => |r - s| * ‖b r - b s‖) =o[𝓝 s] fun r => r - s := by
    have h1 : (fun r : ℝ => |r - s|) =O[𝓝 s] (fun r : ℝ => r - s) := by
      simpa [Real.norm_eq_abs] using
        (isBigO_norm_left (f' := fun r : ℝ => r - s) (g := fun r : ℝ => r - s) (l := 𝓝 s)).2
          (isBigO_refl _ _)
    have h := h1.mul_isLittleO hpo
    simpa using h
  have hg : (fun r => K₀ * c₀ * ‖b r - b s - (r - s) • b'‖ +
      K₁ * (‖b s‖ + 1) * ‖a r - a s - (r - s) • a'‖ +
      |r - s| * (K₁ * ‖a'‖ * ‖b r - b s‖) + M * K₂ * ‖a r - a s‖ ^ 2) =o[𝓝 s] fun r => r - s := by
    refine ((((heo.const_mul_left _).add (hdo.const_mul_left _)).add ?_).add
      (h2o.const_mul_left _))
    have := h3o.const_mul_left (K₁ * ‖a'‖)
    refine this.congr_left (fun r => ?_)
    ring
  refine IsBigO.trans_isLittleO ?_ hg
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hMb, hBev] with r h1 h2
  refine (key r h1 h2).trans ?_
  rw [one_mul, Real.norm_eq_abs]
  exact le_abs_self _

end MarkovTriple.BE
