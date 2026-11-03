import Mathlib

/-!
# `L¹`-differentiation of a Nemytskii composition (analytic step in the proof of BGL Thm 3.3.18, p. 164)

The book says "derivation of `Φ` is then justified".  Since `P_s h`, `P_{t-s} f` are only a.e.-classes, we prove the
needed differentiation abstractly: if `u : ℝ → L¹(μ)` is differentiable at `s`, `u ≥ 0`, and `ψ` is `C¹` on `[0,∞)` with
bounded derivative `K₁` and a remainder estimate of the form `|ψ(b)-ψ(a)-ψ'(a)(b-a)| ≤ |b-a| min(K₂|b-a|, 2K₁)`, then for
`k ∈ L^∞`, `r ↦ ∫ k ψ(u_r)` is differentiable at `s` with derivative `∫ k ψ'(u_s) u'`.
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

namespace MarkovTriple.BGL

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- the tail `∫ (|w| - N)⁺ → 0` as `N → ∞` for integrable `w`. -/
lemma tendsto_tail_integral {w : α → ℝ} (hw : Integrable w μ) :
    Tendsto (fun N : ℕ => ∫ x, max (|w x| - N) 0 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun (N : ℕ) x => max (|w x| - N) 0)
    (f := fun _ => (0 : ℝ)) (bound := fun x => |w x|) (fun N => ?_) hw.abs ?_ ?_
  · simpa using h
  · exact ((hw.abs.aestronglyMeasurable.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const)
  · intro N
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  · refine Eventually.of_forall fun x => ?_
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈|w x|⌉₊) fun N hN => ?_
    have : |w x| ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    exact max_eq_right (by linarith)

lemma integrable_rem_bound {Δ : α → ℝ} {K1 K2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hΔ : Integrable Δ μ) :
    Integrable (fun x => |Δ x| * min (K2 * |Δ x|) (2 * K1)) μ := by
  refine (hΔ.abs.const_mul (2 * K1)).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (hΔ.abs.aemeasurable.mul
      ((hΔ.abs.aemeasurable.const_mul K2).min aemeasurable_const)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
      (le_min (by positivity) (by positivity)))]
    have := min_le_right (K2 * |Δ x|) (2 * K1)
    nlinarith [abs_nonneg (Δ x)]

/-- Key estimate: with `Δ_r = u_r - u_s = (r-s) u' + D_r`,
`∫ |Δ| min(K₂|Δ|, 2K₁) ≤ |r-s| (N K₂ ‖Δ‖₁ + 2K₁ τ_N) + 2K₁ ‖D‖₁`. -/
lemma remainder_integral_le {Δ D u' : α → ℝ} {c K1 K2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hΔ : Integrable Δ μ) (hD : Integrable D μ) (hu : Integrable u' μ)
    (hdec : ∀ᵐ x ∂μ, Δ x = c * u' x + D x) (N : ℕ) :
    ∫ x, |Δ x| * min (K2 * |Δ x|) (2 * K1) ∂μ ≤
      |c| * (N * K2 * ∫ x, |Δ x| ∂μ + 2 * K1 * ∫ x, max (|u' x| - N) 0 ∂μ) +
        2 * K1 * ∫ x, |D x| ∂μ := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have iT : Integrable (fun x => max (|u' x| - N) 0) μ := by
    refine hu.abs.mono' ((hu.abs.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
      aestronglyMeasurable_const) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (abs_nonneg _)
  -- pointwise bound
  have pw : ∀ᵐ x ∂μ, |Δ x| * min (K2 * |Δ x|) (2 * K1) ≤
      |c| * (N * K2 * |Δ x| + 2 * K1 * max (|u' x| - N) 0) + 2 * K1 * |D x| := by
    filter_upwards [hdec] with x hx
    set m := min (K2 * |Δ x|) (2 * K1) with hm
    have hm0 : 0 ≤ m := le_min (by positivity) (by positivity)
    have hm1 : m ≤ K2 * |Δ x| := min_le_left _ _
    have hm2 : m ≤ 2 * K1 := min_le_right _ _
    have h1 : |Δ x| ≤ |c| * |u' x| + |D x| := by
      rw [hx]; calc |c * u' x + D x| ≤ |c * u' x| + |D x| := abs_add_le _ _
        _ = _ := by rw [abs_mul]
    have h2 : |Δ x| * m ≤ |c| * |u' x| * m + |D x| * m := by nlinarith
    have h3 : |D x| * m ≤ 2 * K1 * |D x| := by nlinarith [abs_nonneg (D x)]
    have h4 : |u' x| * m ≤ N * K2 * |Δ x| + 2 * K1 * max (|u' x| - N) 0 := by
      by_cases hle : |u' x| ≤ N
      · have : max (|u' x| - N) 0 = 0 := max_eq_right (by linarith)
        rw [this]
        have : |u' x| * m ≤ N * m := mul_le_mul_of_nonneg_right hle hm0
        nlinarith [abs_nonneg (Δ x)]
      · push Not at hle
        have e : max (|u' x| - N) 0 = |u' x| - N := max_eq_left (by linarith)
        rw [e]
        have : |u' x| * m = N * m + (|u' x| - N) * m := by ring
        rw [this]
        have a1 : N * m ≤ N * (K2 * |Δ x|) := mul_le_mul_of_nonneg_left hm1 hN
        have a2 : (|u' x| - N) * m ≤ (|u' x| - N) * (2 * K1) :=
          mul_le_mul_of_nonneg_left hm2 (by linarith)
        nlinarith
    have h5 : |c| * |u' x| * m ≤ |c| * (N * K2 * |Δ x| + 2 * K1 * max (|u' x| - N) 0) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h4 (abs_nonneg c)
    linarith
  have iL : Integrable (fun x => |Δ x| * min (K2 * |Δ x|) (2 * K1)) μ := by
    refine (hΔ.abs.const_mul (2 * K1)).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (hΔ.abs.aemeasurable.mul
        ((hΔ.abs.aemeasurable.const_mul K2).min aemeasurable_const)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (le_min (by positivity) (by positivity)))]
      have := min_le_right (K2 * |Δ x|) (2 * K1)
      nlinarith [abs_nonneg (Δ x)]
  have iR : Integrable (fun x => |c| * (N * K2 * |Δ x| + 2 * K1 * max (|u' x| - N) 0) +
      2 * K1 * |D x|) μ :=
    (((hΔ.abs.const_mul (N * K2)).add (iT.const_mul (2 * K1))).const_mul |c|).add (hD.abs.const_mul _)
  refine (integral_mono_ae iL iR pw).trans (le_of_eq ?_)
  have i1 : Integrable (fun x => N * K2 * |Δ x| + 2 * K1 * max (|u' x| - N) 0) μ :=
    (hΔ.abs.const_mul (N * K2)).add (iT.const_mul (2 * K1))
  rw [integral_add (i1.const_mul |c|) (hD.abs.const_mul _), integral_const_mul,
    integral_add (hΔ.abs.const_mul (N * K2)) (iT.const_mul (2 * K1)), integral_const_mul,
    integral_const_mul, integral_const_mul]


/-- **`L¹`-differentiability of the Nemytskii composition against a bounded multiplier.** -/
theorem hasDerivAt_integral_comp {ψ ψ' : ℝ → ℝ} {K1 K2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hψm : Measurable ψ) (hψ'm : Measurable ψ') (hψ0 : ψ 0 = 0)
    (hψ' : ∀ a, 0 ≤ a → |ψ' a| ≤ K1)
    (hrem : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      |ψ b - ψ a - ψ' a * (b - a)| ≤ |b - a| * min (K2 * |b - a|) (2 * K1))
    {u : ℝ → Lp ℝ 1 μ} {u' : Lp ℝ 1 μ} {s : ℝ} (hu : HasDerivAt u u' s)
    (hnn : ∀ r, 0 ≤ᵐ[μ] (u r : α → ℝ))
    {k : α → ℝ} {M : ℝ} (hM : 0 ≤ M) (hkm : AEStronglyMeasurable k μ) (hk : ∀ᵐ x ∂μ, |k x| ≤ M) :
    HasDerivAt (fun r => ∫ x, k x * ψ (u r x) ∂μ)
      (∫ x, k x * (ψ' (u s x) * u' x) ∂μ) s := by
  have iu : ∀ r, Integrable (u r : α → ℝ) μ := fun r => L1.integrable_coeFn (u r)
  -- |ψ b| ≤ 3 K1 b for b ≥ 0
  have hψb : ∀ b : ℝ, 0 ≤ b → |ψ b| ≤ 3 * K1 * b := by
    intro b hb
    have := hrem 0 b le_rfl hb
    simp only [hψ0, sub_zero, abs_of_nonneg hb] at this
    have h0 := hψ' 0 le_rfl
    have h1 : |ψ b| ≤ |ψ b - ψ' 0 * b| + |ψ' 0 * b| := by
      have := abs_add_le (ψ b - ψ' 0 * b) (ψ' 0 * b); simpa using this
    have h2 : |ψ' 0 * b| ≤ K1 * b := by rw [abs_mul, abs_of_nonneg hb]; exact mul_le_mul_of_nonneg_right h0 hb
    have h3 : b * min (K2 * b) (2 * K1) ≤ b * (2 * K1) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hb
    linarith [this.trans h3]
  have iψ : ∀ r, Integrable (fun x => ψ (u r x)) μ := by
    intro r
    refine ((iu r).const_mul (3 * K1)).mono' (hψm.comp_aemeasurable (iu r).aemeasurable).aestronglyMeasurable ?_
    filter_upwards [hnn r] with x hx
    rw [Real.norm_eq_abs]; exact (hψb _ hx).trans (le_of_eq (by ring))
  have iψ' : Integrable (fun x => ψ' (u s x) * u' x) μ := by
    refine (L1.integrable_coeFn u').bdd_mul (c := K1) ?_ ?_
    · exact (hψ'm.comp_aemeasurable (iu s).aemeasurable).aestronglyMeasurable
    · filter_upwards [hnn s] with x hx
      rw [Real.norm_eq_abs]; exact hψ' _ hx
  have ik : ∀ g : α → ℝ, Integrable g μ → Integrable (fun x => k x * g x) μ := fun g hg => by
    have := hg.bdd_mul (c := M) hkm (by filter_upwards [hk] with x hx; simpa using hx)
    simpa [mul_comm] using this
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  -- choose N
  have hτ := tendsto_tail_integral (L1.integrable_coeFn u')
  have hτ' : ∀ᶠ N : ℕ in atTop, 2 * M * K1 * ∫ x, max (|u' x| - N) 0 ∂μ ≤ c / 3 := by
    have := hτ.const_mul (2 * M * K1)
    rw [mul_zero] at this
    exact this.eventually (Iic_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := hτ'.exists
  set τ := ∫ x, max (|u' x| - N) 0 ∂μ with hτdef
  -- the norms
  have hDo := (hasDerivAt_iff_isLittleO.1 hu)
  have hcont : Tendsto (fun r => ‖u r - u s‖) (𝓝 s) (𝓝 0) := by
    have := hu.continuousAt.tendsto
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 this)
  have hA : ∀ᶠ r in 𝓝 s, M * N * K2 * ‖u r - u s‖ ≤ c / 3 := by
    have := hcont.const_mul (M * N * K2)
    rw [mul_zero] at this
    exact this.eventually (Iic_mem_nhds (by positivity))
  have hB : ∀ᶠ r in 𝓝 s, ‖u r - u s - (r - s) • u'‖ ≤ (c / (9 * (M * K1 + 1))) * ‖r - s‖ :=
    Asymptotics.isLittleO_iff.1 hDo (by positivity)
  filter_upwards [hA, hB] with r hAr hBr
  set D : Lp ℝ 1 μ := u r - u s - (r - s) • u' with hDdef
  set Δ : Lp ℝ 1 μ := u r - u s with hΔdef
  have hDa : ∀ᵐ x ∂μ, (D : α → ℝ) x = u r x - u s x - (r - s) * u' x := by
    filter_upwards [Lp.coeFn_sub (u r - u s) ((r - s) • u'), Lp.coeFn_sub (u r) (u s),
      Lp.coeFn_smul (r - s) u'] with x h1 h2 h3
    show ((u r - u s - (r - s) • u' : Lp ℝ 1 μ) : α → ℝ) x = _
    rw [h1]; simp only [Pi.sub_apply]; rw [h2, h3]; simp
  have hΔa : ∀ᵐ x ∂μ, (Δ : α → ℝ) x = u r x - u s x := by
    filter_upwards [Lp.coeFn_sub (u r) (u s)] with x h1
    show ((u r - u s : Lp ℝ 1 μ) : α → ℝ) x = _
    rw [h1]; simp
  have hdec : ∀ᵐ x ∂μ, (Δ : α → ℝ) x = (r - s) * u' x + (D : α → ℝ) x := by
    filter_upwards [hDa, hΔa] with x h1 h2; rw [h2]; linarith
  have nΔ : ∫ x, |(Δ : α → ℝ) x| ∂μ = ‖Δ‖ := by
    rw [L1.norm_eq_integral_norm]; simp
  have nD : ∫ x, |(D : α → ℝ) x| ∂μ = ‖D‖ := by
    rw [L1.norm_eq_integral_norm]; simp
  have key := remainder_integral_le hK1 hK2 (L1.integrable_coeFn Δ) (L1.integrable_coeFn D)
    (L1.integrable_coeFn u') hdec N
  rw [nΔ, nD] at key
  set R : α → ℝ := fun x => ψ (u r x) - ψ (u s x) - ψ' (u s x) * (u r x - u s x) with hR
  have hRle : ∀ᵐ x ∂μ, |R x| ≤ |(Δ : α → ℝ) x| * min (K2 * |(Δ : α → ℝ) x|) (2 * K1) := by
    filter_upwards [hnn r, hnn s, hΔa] with x h1 h2 h3
    rw [h3]; exact hrem _ _ h2 h1
  have iψ's : Integrable (fun x => ψ' (u s x) * (u r x - u s x)) μ := by
    have := ((iu r).sub (iu s)).bdd_mul (c := K1)
      (hψ'm.comp_aemeasurable (iu s).aemeasurable).aestronglyMeasurable
      (by filter_upwards [hnn s] with x hx; rw [Real.norm_eq_abs]; exact hψ' _ hx)
    simpa [mul_comm] using this
  have iR : Integrable R μ := ((iψ r).sub (iψ s)).sub iψ's
  have iD : Integrable (fun x => ψ' (u s x) * (D : α → ℝ) x) μ :=
    (L1.integrable_coeFn D).bdd_mul (c := K1)
      (hψ'm.comp_aemeasurable (iu s).aemeasurable).aestronglyMeasurable
      (by filter_upwards [hnn s] with x hx; rw [Real.norm_eq_abs]; exact hψ' _ hx)
  have hI1 : Integrable (fun x => k x * ψ (u r x) - k x * ψ (u s x)) μ :=
    (ik _ (iψ r)).sub (ik _ (iψ s))
  have hI2 : Integrable (fun x => (r - s) * (k x * (ψ' (u s x) * u' x))) μ :=
    (ik _ iψ').const_mul _
  have hF : (∫ x, k x * ψ (u r x) ∂μ) - (∫ x, k x * ψ (u s x) ∂μ) -
      (r - s) • ∫ x, k x * (ψ' (u s x) * u' x) ∂μ =
      ∫ x, k x * (R x + ψ' (u s x) * (D : α → ℝ) x) ∂μ := by
    have e1 : (∫ x, k x * ψ (u r x) ∂μ) - (∫ x, k x * ψ (u s x) ∂μ) =
        ∫ x, (k x * ψ (u r x) - k x * ψ (u s x)) ∂μ := (integral_sub (ik _ (iψ r)) (ik _ (iψ s))).symm
    have e2 : (r - s) • ∫ x, k x * (ψ' (u s x) * u' x) ∂μ =
        ∫ x, (r - s) * (k x * (ψ' (u s x) * u' x)) ∂μ := by
      rw [smul_eq_mul, integral_const_mul]
    rw [e1, e2, ← integral_sub hI1 hI2]
    refine integral_congr_ae ?_
    filter_upwards [hDa] with x hx
    simp only [hR, hx]; ring
  have hbd : ‖(∫ x, k x * ψ (u r x) ∂μ) - (∫ x, k x * ψ (u s x) ∂μ) -
      (r - s) • ∫ x, k x * (ψ' (u s x) * u' x) ∂μ‖ ≤
      M * ∫ x, |R x| ∂μ + M * K1 * ‖D‖ := by
    rw [hF]
    refine (norm_integral_le_integral_norm _).trans ?_
    have iRa : Integrable (fun x => |R x|) μ := iR.abs
    have iDa : Integrable (fun x => |(D : α → ℝ) x|) μ := (L1.integrable_coeFn D).abs
    calc ∫ x, ‖k x * (R x + ψ' (u s x) * (D : α → ℝ) x)‖ ∂μ
        ≤ ∫ x, (M * |R x| + M * K1 * |(D : α → ℝ) x|) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
            ((iRa.const_mul M).add (iDa.const_mul _)) ?_
          filter_upwards [hk, hnn s] with x h1 h2
          have h3 := hψ' _ h2
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          have h4 : |R x + ψ' (u s x) * (D : α → ℝ) x| ≤ |R x| + K1 * |(D : α → ℝ) x| :=
            (abs_add_le _ _).trans (by
              rw [abs_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right h3 (abs_nonneg _)))
          calc |k x| * |R x + ψ' (u s x) * (D : α → ℝ) x|
              ≤ M * (|R x| + K1 * |(D : α → ℝ) x|) :=
                mul_le_mul h1 h4 (abs_nonneg _) hM
            _ = _ := by ring
      _ = _ := by
          rw [integral_add (iRa.const_mul M) (iDa.const_mul _), integral_const_mul,
            integral_const_mul, nD]
  have hRint : ∫ x, |R x| ∂μ ≤ ∫ x, |(Δ : α → ℝ) x| * min (K2 * |(Δ : α → ℝ) x|) (2 * K1) ∂μ := by
    refine integral_mono_ae iR.abs (integrable_rem_bound hK1 hK2 (L1.integrable_coeFn Δ)) hRle
  rw [Real.norm_eq_abs] at hBr ⊢
  have hq : 0 ≤ c / (9 * (M * K1 + 1)) := by positivity
  have hq2 : (c / (9 * (M * K1 + 1))) * (M * K1 + 1) = c / 9 := by
    field_simp
  have hd0 : 0 ≤ ‖D‖ := norm_nonneg _
  have ht : 0 ≤ |r - s| := abs_nonneg _
  have hMK : 0 ≤ M * K1 := mul_nonneg hM hK1
  have e1 : M * ‖D‖ * (2 * K1) + M * K1 * ‖D‖ = 3 * (M * K1) * ‖D‖ := by ring
  have e2 : (M * K1) * (c / (9 * (M * K1 + 1))) ≤ c / 9 := by
    nlinarith
  have e3 : ‖D‖ ≤ (c / (9 * (M * K1 + 1))) * |r - s| := by simpa using hBr
  have e4 : 3 * (M * K1) * ‖D‖ ≤ (c / 3) * |r - s| := by
    have := mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ 3 * (M * K1))
    have h5 : 3 * (M * K1) * ((c / (9 * (M * K1 + 1))) * |r - s|) ≤ (c / 3) * |r - s| := by
      have : 3 * (M * K1) * (c / (9 * (M * K1 + 1))) ≤ c / 3 := by nlinarith
      nlinarith
    linarith
  have e5 : M * (|r - s| * (N * K2 * ‖Δ‖ + 2 * K1 * τ)) ≤ (2 * c / 3) * |r - s| := by
    have hh : M * (N * K2 * ‖Δ‖ + 2 * K1 * τ) ≤ 2 * c / 3 := by nlinarith
    nlinarith
  have hh2 := mul_le_mul_of_nonneg_left (le_trans hRint key) hM
  have hh3 : M * (|r - s| * (N * K2 * ‖Δ‖ + 2 * K1 * τ) + 2 * K1 * ‖D‖) =
      M * (|r - s| * (N * K2 * ‖Δ‖ + 2 * K1 * τ)) + M * ‖D‖ * (2 * K1) := by ring
  rw [Real.norm_eq_abs] at hbd
  rw [← hτdef] at hh2
  have hr : ‖r - s‖ = |r - s| := Real.norm_eq_abs _
  rw [hr]
  have hc3 : (2 * c / 3) * |r - s| + (c / 3) * |r - s| = c * |r - s| := by ring
  linarith

section Pairing

variable {ψ ψ' : ℝ → ℝ}

lemma memLp_two_comp (hψm : Measurable ψ) (hψ0 : ψ 0 = 0)
    (hH : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (ψ b - ψ a) ^ 2 ≤ |b - a|)
    (v : Lp ℝ 1 μ) (hv : 0 ≤ᵐ[μ] (v : α → ℝ)) : MemLp (fun x => ψ (v x)) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => ψ (v x)) μ :=
    (hψm.comp_aemeasurable (L1.integrable_coeFn v).aemeasurable).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine (L1.integrable_coeFn v).mono' (hm.pow 2) ?_
  filter_upwards [hv] with x hx
  have := hH 0 (v x) le_rfl hx
  rw [hψ0, sub_zero, sub_zero, abs_of_nonneg hx] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact this

/-- the `L²`-class of `ψ ∘ v`. -/
noncomputable def psiCls (hψm : Measurable ψ) (hψ0 : ψ 0 = 0)
    (hH : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (ψ b - ψ a) ^ 2 ≤ |b - a|)
    (v : Lp ℝ 1 μ) (hv : 0 ≤ᵐ[μ] (v : α → ℝ)) : Lp ℝ 2 μ :=
  (memLp_two_comp hψm hψ0 hH v hv).toLp _

lemma norm_psiCls_sub_le (hψm : Measurable ψ) (hψ0 : ψ 0 = 0)
    (hH : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (ψ b - ψ a) ^ 2 ≤ |b - a|)
    (v w : Lp ℝ 1 μ) (hv : 0 ≤ᵐ[μ] (v : α → ℝ)) (hw : 0 ≤ᵐ[μ] (w : α → ℝ)) :
    ‖psiCls hψm hψ0 hH v hv - psiCls hψm hψ0 hH w hw‖ ≤ Real.sqrt ‖v - w‖ := by
  set d := psiCls hψm hψ0 hH v hv - psiCls hψm hψ0 hH w hw with hd
  have h1 : ‖d‖ ^ 2 = ∫ x, (d : α → ℝ) x * (d : α → ℝ) x ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sq]
  have h2 : ‖v - w‖ = ∫ x, |(v : α → ℝ) x - (w : α → ℝ) x| ∂μ := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub v w] with x hx
    rw [hx]; simp
  have h3 : ∫ x, (d : α → ℝ) x * (d : α → ℝ) x ∂μ ≤ ∫ x, |(v : α → ℝ) x - (w : α → ℝ) x| ∂μ := by
    have iv := L1.integrable_coeFn v
    have iw := L1.integrable_coeFn w
    have i2 : Integrable (fun x => (d : α → ℝ) x * (d : α → ℝ) x) μ := by
      have := (Lp.memLp d).integrable_sq
      simpa [sq] using this
    refine integral_mono_ae i2 (iv.sub iw).abs ?_
    filter_upwards [Lp.coeFn_sub (psiCls hψm hψ0 hH v hv) (psiCls hψm hψ0 hH w hw),
      (memLp_two_comp hψm hψ0 hH v hv).coeFn_toLp, (memLp_two_comp hψm hψ0 hH w hw).coeFn_toLp,
      hv, hw] with x e1 e2 e3 h4 h5
    rw [hd, e1]
    simp only [Pi.sub_apply, psiCls, e2, e3]
    have := hH _ _ h5 h4
    rw [← sq]; exact this
  rw [← h2] at h3
  refine Real.le_sqrt_of_sq_le ?_
  rw [h1]; exact h3

end Pairing

end MarkovTriple.BGL
