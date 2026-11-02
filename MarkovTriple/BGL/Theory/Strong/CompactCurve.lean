import Mathlib
import MarkovTriple.BGL.Theory.Strong.Remainder
import MarkovTriple.BGL.Theory.Compact.Gradient
import MarkovTriple.BGL.Theory.Compact.Chain
import MarkovTriple.BGL.Theory.Compact.Entropy

/-!
# `L²`-differentiability of `s ↦ [Γ(P_{t-s} f)]` on a compact triple

For a compact triple (`𝒜 = 𝒜₀`, `μ` finite) and `f ∈ 𝒜₀`, the curve `r ↦ [Γ(P_{t-r} f)] ∈ L²(μ)` is
differentiable at `s ∈ (0,t)` with derivative `[2Γ(g_s, g_s')]`, `g_s = P_{t-s} f`, `g_s' = -L g_s`,
under `CD(ρ,n)` (used only through the weak gradient bound, which provides the uniform bound
`‖Γ(g_r)‖_∞ ≤ B`).  The proof is the energy estimate `‖Γ(a,b)‖₂² ≤ ‖Γ b‖_∞ ℰ(a)` and `ℰ(a) ≤ ‖a‖‖La‖`
applied to the second-order Taylor remainder `ρ_r = g_r − g_s − (r-s) g_s'` of the `L²`-smooth orbit.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped NNReal ENNReal InnerProductSpace
open MarkovTriple.BGL.Compact

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace CompactTriple

variable (C : CompactTriple E)

/-- `P_{t-r} f` as a test function. -/
noncomputable def ppt (f : C.A₀) (t : ℝ≥0) (r : ℝ) : E → ℝ := C.Pt ((t : ℝ) - r).toNNReal f

lemma ppt_mem (f : C.A₀) (t : ℝ≥0) (r : ℝ) : C.ppt f t r ∈ C.A₀ := C.Pt_mem _ f

lemma G_mem₀ {a b : E → ℝ} (ha : a ∈ C.A₀) (hb : b ∈ C.A₀) :
    FullTriple.G C.toFullTriple a b ∈ C.A₀ :=
  FullTriple.ΓA_mem_A₀ C.toFullTriple (C.A₀_le a ha) hb

/-- `r ↦ [Γ(P_{t-r} f)]`. -/
noncomputable def ucls (f : C.A₀) (t : ℝ≥0) (r : ℝ) : Lp ℝ 2 C.μ :=
  C.toDiffusionTriple.cls ⟨FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r),
    C.G_mem₀ (C.ppt_mem f t r) (C.ppt_mem f t r)⟩

/-- `g_s' = -L g_s`. -/
noncomputable def gder (f : C.A₀) (t : ℝ≥0) (s : ℝ) : E → ℝ := (-1 : ℝ) • C.L (C.ppt f t s)

lemma gder_mem (f : C.A₀) (t : ℝ≥0) (s : ℝ) : C.gder f t s ∈ C.A₀ :=
  C.A₀.smul_mem _ (C.Lm (C.ppt_mem f t s))

/-- the candidate derivative `[2Γ(g_s, g_s')]`. -/
noncomputable def uder (f : C.A₀) (t : ℝ≥0) (s : ℝ) : Lp ℝ 2 C.μ :=
  C.toDiffusionTriple.cls ⟨(2 : ℝ) • FullTriple.G C.toFullTriple (C.ppt f t s) (C.gder f t s),
    C.A₀.smul_mem _ (C.G_mem₀ (C.ppt_mem f t s) (C.gder_mem f t s))⟩

/-- uniform bound `Γ(P_τ f) ≤ B` for `0 ≤ τ ≤ t` under `CD(ρ,n)`. -/
theorem Gbound {ρ : ℝ} {n : ℝ≥0∞} (hCD : C.toFullTriple.CD ρ n) (f : C.A₀) (t : ℝ≥0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, -1 ≤ r →
      FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r) ≤ᵐ[C.μ] fun _ => B := by
  obtain ⟨cf, hcf0, hcf⟩ := C.exists_bound ⟨FullTriple.G C.toFullTriple f.1 f.1,
    C.G_mem₀ f.2 f.2⟩
  refine ⟨Real.exp (2 * |ρ| * (t + 1)) * cf, by positivity, fun r hr0 => ?_⟩
  set τ : ℝ≥0 := ((t : ℝ) - r).toNNReal with hτ
  have hτle : (τ : ℝ) ≤ t + 1 := by
    have : ((t : ℝ) - r).toNNReal ≤ ((t : ℝ) + 1).toNNReal :=
      Real.toNNReal_le_toNNReal (by linarith)
    have h2 : (((t : ℝ) + 1).toNNReal : ℝ) = t + 1 := Real.coe_toNNReal _ (by positivity)
    have h3 : ((((t : ℝ) - r).toNNReal : ℝ)) ≤ ((((t : ℝ) + 1).toNNReal : ℝ)) := this
    rw [h2] at h3; exact h3
  have hgb := compact_gradient_bound C hCD f τ
  have hc : ∀ᵐ x ∂C.μ, |(C.toDiffusionTriple.cls ⟨FullTriple.G C.toFullTriple f.1 f.1,
      C.ΓA_self_mem_A₀ f.2⟩ : E → ℝ) x| ≤ cf := by
    filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨FullTriple.G C.toFullTriple f.1 f.1,
      C.ΓA_self_mem_A₀ f.2⟩] with x hx
    rw [hx]; exact hcf x
  have hs := C.ae_abs_semigroup_le hcf0 hc τ
  filter_upwards [hgb, hs] with x h1 h2
  show FullTriple.G C.toFullTriple (C.Pt τ f) (C.Pt τ f) x ≤ _
  refine h1.trans ?_
  have hexp : Real.exp (-2 * ρ * τ) ≤ Real.exp (2 * |ρ| * (t + 1)) := by
    apply Real.exp_le_exp.2
    have h5 : -2 * ρ * τ ≤ 2 * |ρ| * τ := by nlinarith [neg_abs_le ρ, τ.2]
    have h6 : 2 * |ρ| * τ ≤ 2 * |ρ| * (t + 1) := by nlinarith [abs_nonneg ρ]
    linarith
  calc Real.exp (-2 * ρ * τ) * ((C.toDiffusionTriple.semigroup τ (C.toDiffusionTriple.cls
          ⟨C.toDiffusionTriple.ΓA f.1 f.1, C.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 C.μ) x)
      ≤ Real.exp (-2 * ρ * τ) * |((C.toDiffusionTriple.semigroup τ (C.toDiffusionTriple.cls
          ⟨C.toDiffusionTriple.ΓA f.1 f.1, C.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 C.μ) x)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
    _ ≤ Real.exp (2 * |ρ| * (t + 1)) * cf := mul_le_mul hexp h2 (abs_nonneg _) (Real.exp_pos _).le

/-- the second-order Taylor remainder `ρ_r = g_r − g_s − (r−s) g_s'` -/
noncomputable def rho (f : C.A₀) (t : ℝ≥0) (s r : ℝ) : E → ℝ :=
  fun x => (C.ppt f t r x + (-1) * C.ppt f t s x) + (-(r - s)) * C.gder f t s x

lemma rho_mem (f : C.A₀) (t : ℝ≥0) (s r : ℝ) : C.rho f t s r ∈ C.A₀ := by
  have : C.rho f t s r = (C.ppt f t r + (-1 : ℝ) • C.ppt f t s) + (-(r - s)) • C.gder f t s := by
    funext x; simp [rho]
  rw [this]
  exact C.A₀.add_mem (C.A₀.add_mem (C.ppt_mem f t r) (C.A₀.smul_mem _ (C.ppt_mem f t s)))
    (C.A₀.smul_mem _ (C.gder_mem f t s))

lemma ppt_eq (f : C.A₀) (t : ℝ≥0) (s r : ℝ) :
    C.ppt f t r = fun w => C.ppt f t s w + (r - s) * C.gder f t s w + C.rho f t s r w := by
  funext w; simp only [rho]; ring

/-- `E1 r`, `E2 r`: the Taylor remainders of the `L²`-orbits. -/
noncomputable def E1 (f : C.A₀) (t : ℝ≥0) (s r : ℝ) : Lp ℝ 2 C.μ :=
  C.orb f (t - r) - C.orb f (t - s) - (r - s) • (-(C.orb (C.Lt f) (t - s)))

noncomputable def E2 (f : C.A₀) (t : ℝ≥0) (s r : ℝ) : Lp ℝ 2 C.μ :=
  C.orb (C.Lt f) (t - r) - C.orb (C.Lt f) (t - s) -
    (r - s) • (-(C.orb (C.Lt (C.Lt f)) (t - s)))

lemma cls_rho (f : C.A₀) (t : ℝ≥0) (s r : ℝ) :
    C.toDiffusionTriple.cls ⟨C.rho f t s r, C.rho_mem f t s r⟩ = C.E1 f t s r := by
  refine Lp.ext ?_
  have h1 := C.orb_ae f (t - r)
  have h2 := C.orb_ae f (t - s)
  have h3 := C.L_Pt f ((t : ℝ) - s)
  filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨C.rho f t s r, C.rho_mem f t s r⟩,
    Lp.coeFn_sub (C.orb f (t - r) - C.orb f (t - s)) ((r - s) • (-(C.orb (C.Lt f) (t - s)))),
    Lp.coeFn_sub (C.orb f (t - r)) (C.orb f (t - s)),
    Lp.coeFn_smul (r - s) (-(C.orb (C.Lt f) (t - s))), Lp.coeFn_neg (C.orb (C.Lt f) (t - s)),
    h1, h2, h3] with x a1 a2 a3 a4 a5 b1 b2 b3
  rw [a1]
  show C.rho f t s r x = (C.E1 f t s r : E → ℝ) x
  unfold E1
  rw [a2, Pi.sub_apply, a3, Pi.sub_apply, a4, Pi.smul_apply, a5, Pi.neg_apply, b1, b2]
  simp only [rho, gder, ppt, Pi.smul_apply, smul_eq_mul]
  rw [← b3]
  ring

lemma cls_Lrho (f : C.A₀) (t : ℝ≥0) (s r : ℝ) :
    C.toDiffusionTriple.cls ⟨C.L (C.rho f t s r), C.Lm (C.rho_mem f t s r)⟩ = C.E2 f t s r := by
  refine Lp.ext ?_
  have hA1 : C.ppt f t r ∈ C.A := C.A₀_le _ (C.ppt_mem f t r)
  have hA2 : C.ppt f t s ∈ C.A := C.A₀_le _ (C.ppt_mem f t s)
  have hA3 : C.gder f t s ∈ C.A := C.A₀_le _ (C.gder_mem f t s)
  have hA12 : (fun x => C.ppt f t r x + (-1) * C.ppt f t s x) ∈ C.A := by
    have : (fun x => C.ppt f t r x + (-1) * C.ppt f t s x) = C.ppt f t r + (-1 : ℝ) • C.ppt f t s := by
      funext x; simp
    rw [this]; exact C.A.add_mem hA1 (C.A.smul_mem hA2 _)
  have l1 := FullTriple.L_lin (T := C.toFullTriple) hA12 hA3 (-(r - s))
  have l2 := FullTriple.L_lin (T := C.toFullTriple) hA1 hA2 (-1)
  have hLs : C.L (C.ppt f t s) ∈ C.A := C.A₀_le _ (C.Lm (C.ppt_mem f t s))
  have h0 : (fun _ : E => (0 : ℝ)) ∈ C.A := C.A.algebraMap_mem 0
  have l3 := FullTriple.L_lin (T := C.toFullTriple) h0 hLs (-1)
  have l4 := FullTriple.L_const (T := C.toFullTriple) 0
  have eg : C.gder f t s = fun x => (fun _ : E => (0 : ℝ)) x + (-1) * C.L (C.ppt f t s) x := by
    funext x; simp [gder]
  have h1 := C.L_Pt f ((t : ℝ) - r)
  have h2 := C.L_Pt f ((t : ℝ) - s)
  have h3 := C.L_Pt2 f ((t : ℝ) - s)
  filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple
      ⟨C.L (C.rho f t s r), C.Lm (C.rho_mem f t s r)⟩,
    Lp.coeFn_sub (C.orb (C.Lt f) (t - r) - C.orb (C.Lt f) (t - s))
      ((r - s) • (-(C.orb (C.Lt (C.Lt f)) (t - s)))),
    Lp.coeFn_sub (C.orb (C.Lt f) (t - r)) (C.orb (C.Lt f) (t - s)),
    Lp.coeFn_smul (r - s) (-(C.orb (C.Lt (C.Lt f)) (t - s))),
    Lp.coeFn_neg (C.orb (C.Lt (C.Lt f)) (t - s)), h1, h2, h3, l1, l2, l3, l4] with
    x a1 a2 a3 a4 a5 b1 b2 b3 c1 c2 c3 c4
  rw [a1]
  show C.L (C.rho f t s r) x = (C.E2 f t s r : E → ℝ) x
  unfold E2
  rw [a2, Pi.sub_apply, a3, Pi.sub_apply, a4, Pi.smul_apply, a5, Pi.neg_apply, ← b1, ← b2, ← b3]
  have e : C.L (C.rho f t s r) x = C.L (fun x => (C.ppt f t r x + (-1) * C.ppt f t s x) +
      (-(r - s)) * C.gder f t s x) x := rfl
  rw [e, c1]
  have e3 : C.L (C.gder f t s) x = (-1) * C.L (C.L (C.ppt f t s)) x := by
    rw [eg]
    have := c3
    simp only [Pi.zero_apply] at c4
    rw [this, c4]; ring
  rw [e3, c2]
  simp only [smul_eq_mul, ppt]
  ring

lemma int_G_nonneg {a : E → ℝ} (ha : a ∈ C.A₀) :
    0 ≤ ∫ x, FullTriple.G C.toFullTriple a a x ∂C.μ :=
  integral_nonneg_of_ae (C.ΓA_nonneg a (C.A₀_le a ha))

lemma X_ae (f : C.A₀) (t : ℝ≥0) (s r : ℝ) :
    ((C.ucls f t r - C.ucls f t s - (r - s) • C.uder f t s : Lp ℝ 2 C.μ) : E → ℝ) =ᵐ[C.μ]
      fun w => FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r) w -
        FullTriple.G C.toFullTriple (C.ppt f t s) (C.ppt f t s) w -
        2 * (r - s) * FullTriple.G C.toFullTriple (C.ppt f t s) (C.gder f t s) w := by
  filter_upwards [Lp.coeFn_sub (C.ucls f t r - C.ucls f t s) ((r - s) • C.uder f t s),
    Lp.coeFn_sub (C.ucls f t r) (C.ucls f t s), Lp.coeFn_smul (r - s) (C.uder f t s),
    DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨FullTriple.G C.toFullTriple (C.ppt f t r)
      (C.ppt f t r), C.G_mem₀ (C.ppt_mem f t r) (C.ppt_mem f t r)⟩,
    DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨FullTriple.G C.toFullTriple (C.ppt f t s)
      (C.ppt f t s), C.G_mem₀ (C.ppt_mem f t s) (C.ppt_mem f t s)⟩,
    DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨(2 : ℝ) • FullTriple.G C.toFullTriple
      (C.ppt f t s) (C.gder f t s), C.A₀.smul_mem _ (C.G_mem₀ (C.ppt_mem f t s) (C.gder_mem f t s))⟩]
    with w a1 a2 a3 a4 a5 a6
  rw [a1, Pi.sub_apply, a2, Pi.sub_apply, a3, Pi.smul_apply]
  unfold ucls uder
  rw [a4, a5, a6]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **`L²`-differentiability of `r ↦ [Γ(P_{t-r} f)]`.** -/
theorem hasDerivAt_ucls {ρ : ℝ} {n : ℝ≥0∞} (hCD : C.toFullTriple.CD ρ n) (f : C.A₀) (t : ℝ≥0)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) : HasDerivAt (C.ucls f t) (C.uder f t s) s := by
  have hts : 0 < (t : ℝ) - s := sub_pos.2 hs.2
  obtain ⟨B, hB0, hB⟩ := C.Gbound hCD f t
  obtain ⟨B', hB'0, hB'⟩ := C.exists_bound ⟨FullTriple.G C.toFullTriple (C.gder f t s) (C.gder f t s),
    C.G_mem₀ (C.gder_mem f t s) (C.gder_mem f t s)⟩
  set K₁ : ℝ := ∫ w, (FullTriple.G C.toFullTriple (C.gder f t s) (C.gder f t s) w) ^ 2 ∂C.μ with hK₁
  have hK₁0 : 0 ≤ K₁ := integral_nonneg fun w => sq_nonneg _
  have o1 : (fun r => ‖C.E1 f t s r‖) =o[𝓝 s] fun r => r - s :=
    (hasDerivAt_iff_isLittleO.1 (C.hasDerivAt_orb_comp f (t : ℝ) hts)).norm_left
  have o2 : (fun r => ‖C.E2 f t s r‖) =o[𝓝 s] fun r => r - s :=
    (hasDerivAt_iff_isLittleO.1 (C.hasDerivAt_orb_comp (C.Lt f) (t : ℝ) hts)).norm_left
  have o12 : (fun r => ‖C.E1 f t s r‖ * ‖C.E2 f t s r‖) =o[𝓝 s] fun r => (r - s) * (r - s) :=
    o1.mul o2
  have o4 : (fun r : ℝ => (r - s) ^ 4) =o[𝓝 s] fun r => (r - s) * (r - s) := by
    have h := (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (m := 2) (n := 4) (by norm_num))
    have hc : Tendsto (fun r : ℝ => r - s) (𝓝 s) (𝓝 0) := by
      have : Continuous fun r : ℝ => r - s := continuous_id.sub continuous_const
      simpa using this.tendsto s
    have := h.comp_tendsto hc
    refine this.congr_right (fun r => ?_)
    simp [sq]
  have osum : (fun r => ‖C.E1 f t s r‖ * ‖C.E2 f t s r‖ + (r - s) ^ 4) =o[𝓝 s]
      fun r => (r - s) * (r - s) := o12.add o4
  -- the pointwise (in r) estimate
  set K : ℝ := 4 * (B + B + B') + 4 * K₁ with hK
  have hbound : ∀ᶠ r in 𝓝 s, ‖‖C.ucls f t r - C.ucls f t s - (r - s) • C.uder f t s‖ ^ 2‖ ≤
      K * ‖‖C.E1 f t s r‖ * ‖C.E2 f t s r‖ + (r - s) ^ 4‖ := by
    have hn : Set.Ioo (0 : ℝ) (min (t : ℝ) (s + 1)) ∩ Set.Ioo (s - 1) (s + 1) ∈ 𝓝 s := by
      refine inter_mem (Ioo_mem_nhds hs.1 (lt_min hs.2 (by linarith))) (Ioo_mem_nhds (by linarith)
        (by linarith))
    filter_upwards [hn] with r hr
    have hr0 : 0 ≤ r := hr.1.1.le
    have hrt : r ≤ t := hr.1.2.le.trans (min_le_left _ _)
    have hh : |r - s| ≤ 1 := abs_le.2 ⟨by linarith [hr.2.1], by linarith [hr.2.2]⟩
    have hh2 : (r - s) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (r - s), sq_abs (r - s)]
    set X := C.ucls f t r - C.ucls f t s - (r - s) • C.uder f t s with hX
    have hXnorm : ‖X‖ ^ 2 = ∫ w, (FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r) w -
        FullTriple.G C.toFullTriple (C.ppt f t s) (C.ppt f t s) w -
        2 * (r - s) * FullTriple.G C.toFullTriple (C.ppt f t s) (C.gder f t s) w) ^ 2 ∂C.μ := by
      rw [← Compact.integral_sq_eq]
      refine integral_congr_ae ?_
      filter_upwards [C.X_ae f t s r] with w hw
      rw [hw]
    have hrem := FullTriple.remainder_sq_le (T := C.toFullTriple) (C.ppt_mem f t s) (C.gder_mem f t s)
      (C.rho_mem f t s r) (C.ppt_mem f t r) (r - s) (C.ppt_eq f t s r) (B := B) (B' := B')
      (hB s (by linarith [hs.1])) (hB r (by linarith))
      (Eventually.of_forall fun w => (le_abs_self _).trans (hB' w))
    have hE : ∫ w, FullTriple.G C.toFullTriple (C.rho f t s r) (C.rho f t s r) w ∂C.μ ≤
        ‖C.E1 f t s r‖ * ‖C.E2 f t s r‖ := by
      have := FullTriple.int_G_self_le (T := C.toFullTriple) (C.rho_mem f t s r)
      rw [C.cls_rho, C.cls_Lrho] at this
      exact this
    have hE0 := C.int_G_nonneg (C.rho_mem f t s r)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hXnorm,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine hrem.trans ?_
    have hB2 : (B + B + (r - s) ^ 2 * B') * ∫ w, FullTriple.G C.toFullTriple (C.rho f t s r)
        (C.rho f t s r) w ∂C.μ ≤ (B + B + B') * (‖C.E1 f t s r‖ * ‖C.E2 f t s r‖) := by
      have h1 : (B + B + (r - s) ^ 2 * B') ≤ (B + B + B') := by nlinarith
      have h2 : (B + B + B') * ∫ w, FullTriple.G C.toFullTriple (C.rho f t s r)
          (C.rho f t s r) w ∂C.μ ≤ (B + B + B') * (‖C.E1 f t s r‖ * ‖C.E2 f t s r‖) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      calc (B + B + (r - s) ^ 2 * B') * ∫ w, FullTriple.G C.toFullTriple (C.rho f t s r)
            (C.rho f t s r) w ∂C.μ ≤ (B + B + B') * ∫ w, FullTriple.G C.toFullTriple (C.rho f t s r)
            (C.rho f t s r) w ∂C.μ := mul_le_mul_of_nonneg_right h1 hE0
        _ ≤ _ := h2
    have h4 : (r - s) ^ 4 * K₁ ≤ K₁ * (r - s) ^ 4 := le_of_eq (mul_comm _ _)
    have hpe : 0 ≤ ‖C.E1 f t s r‖ * ‖C.E2 f t s r‖ := by positivity
    have hp4 : 0 ≤ (r - s) ^ 4 := by positivity
    nlinarith [hB2, h4, mul_nonneg hB0 hpe, mul_nonneg hK₁0 hp4]
  have hO : (fun r => ‖C.ucls f t r - C.ucls f t s - (r - s) • C.uder f t s‖ ^ 2) =O[𝓝 s]
      fun r => ‖C.E1 f t s r‖ * ‖C.E2 f t s r‖ + (r - s) ^ 4 :=
    Asymptotics.IsBigO.of_bound K (by
      filter_upwards [hbound] with r hr
      simpa [Real.norm_eq_abs] using hr)
  have hsq := hO.trans_isLittleO osum
  refine hasDerivAt_iff_isLittleO.2 ?_
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have := hsq.def (by positivity : 0 < c ^ 2)
  filter_upwards [this] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_of_nonneg
    (by nlinarith [sq_nonneg (r - s)] : 0 ≤ (r - s) * (r - s))] at hr
  rw [Real.norm_eq_abs]
  have h2 : ‖C.ucls f t r - C.ucls f t s - (r - s) • C.uder f t s‖ ^ 2 ≤ (c * |r - s|) ^ 2 := by
    calc _ ≤ c ^ 2 * ((r - s) * (r - s)) := hr
      _ = (c * |r - s|) ^ 2 := by rw [mul_pow, sq_abs]; ring
  have := (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h2
  exact this

/-- `L²`-continuity of `r ↦ [Γ(P_{t-r} f)]` on `[0,∞)` (energy estimate with `h = 0`). -/
theorem continuousAt_ucls {ρ : ℝ} {n : ℝ≥0∞} (hCD : C.toFullTriple.CD ρ n) (f : C.A₀) (t : ℝ≥0)
    {r0 : ℝ} (hr0 : 0 ≤ r0) : ContinuousAt (C.ucls f t) r0 := by
  obtain ⟨B, hB0, hB⟩ := C.Gbound hCD f t
  obtain ⟨B', hB'0, hB'⟩ := C.exists_bound ⟨FullTriple.G C.toFullTriple (C.gder f t r0) (C.gder f t r0),
    C.G_mem₀ (C.gder_mem f t r0) (C.gder_mem f t r0)⟩
  let e1 : ℝ → ℝ := fun r => ‖C.orb f (t - r) - C.orb f (t - r0)‖
  let e2 : ℝ → ℝ := fun r => ‖C.orb (C.Lt f) (t - r) - C.orb (C.Lt f) (t - r0)‖
  have he1 : Tendsto e1 (𝓝 r0) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => C.orb f (t - r) :=
      (C.continuous_orb f).comp (continuous_const.sub continuous_id)
    have := (hc.tendsto r0).sub_const (C.orb f (t - r0))
    have h2 := (continuous_norm.tendsto _).comp this
    simpa [e1, Function.comp_def] using h2
  have he2 : Tendsto e2 (𝓝 r0) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => C.orb (C.Lt f) (t - r) :=
      (C.continuous_orb (C.Lt f)).comp (continuous_const.sub continuous_id)
    have := (hc.tendsto r0).sub_const (C.orb (C.Lt f) (t - r0))
    have h2 := (continuous_norm.tendsto _).comp this
    simpa [e2, Function.comp_def] using h2
  have hsq : ∀ᶠ r in 𝓝 r0, ‖C.ucls f t r - C.ucls f t r0‖ ^ 2 ≤ 8 * B * (e1 r * e2 r) := by
    filter_upwards [Ioi_mem_nhds (by linarith : (-1 : ℝ) < r0)] with r hr
    have hr' : -1 ≤ r := (le_of_lt hr)
    let ρ' : E → ℝ := fun w => C.ppt f t r w + (-1) * C.ppt f t r0 w
    have hρ' : ρ' ∈ C.A₀ := by
      have : ρ' = C.ppt f t r + (-1 : ℝ) • C.ppt f t r0 := by funext w; simp [ρ']
      rw [this]; exact C.A₀.add_mem (C.ppt_mem f t r) (C.A₀.smul_mem _ (C.ppt_mem f t r0))
    have hrem := FullTriple.remainder_sq_le (T := C.toFullTriple) (C.ppt_mem f t r0) (C.gder_mem f t r0)
      hρ' (C.ppt_mem f t r) 0 (by funext w; simp [ρ']) (B := B) (B' := B')
      (hB r0 (by linarith)) (hB r hr')
      (Eventually.of_forall fun w => (le_abs_self _).trans (hB' w))
    have hnorm : ‖C.ucls f t r - C.ucls f t r0‖ ^ 2 = ∫ w,
        (FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r) w -
          FullTriple.G C.toFullTriple (C.ppt f t r0) (C.ppt f t r0) w -
          2 * 0 * FullTriple.G C.toFullTriple (C.ppt f t r0) (C.gder f t r0) w) ^ 2 ∂C.μ := by
      rw [← Compact.integral_sq_eq]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (C.ucls f t r) (C.ucls f t r0),
        DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨FullTriple.G C.toFullTriple (C.ppt f t r)
          (C.ppt f t r), C.G_mem₀ (C.ppt_mem f t r) (C.ppt_mem f t r)⟩,
        DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨FullTriple.G C.toFullTriple (C.ppt f t r0)
          (C.ppt f t r0), C.G_mem₀ (C.ppt_mem f t r0) (C.ppt_mem f t r0)⟩] with w a1 a2 a3
      rw [a1, Pi.sub_apply]
      unfold ucls
      rw [a2, a3]; ring
    have hcls : C.toDiffusionTriple.cls ⟨ρ', hρ'⟩ = C.orb f (t - r) - C.orb f (t - r0) := by
      refine Lp.ext ?_
      filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨ρ', hρ'⟩,
        Lp.coeFn_sub (C.orb f (t - r)) (C.orb f (t - r0)), C.orb_ae f (t - r), C.orb_ae f (t - r0)]
        with w a1 a2 a3 a4
      rw [a1, a2, Pi.sub_apply, a3, a4]
      simp only [ρ', ppt]; ring
    have hLcls : C.toDiffusionTriple.cls ⟨C.L ρ', C.Lm hρ'⟩ =
        C.orb (C.Lt f) (t - r) - C.orb (C.Lt f) (t - r0) := by
      refine Lp.ext ?_
      have hA1 : C.ppt f t r ∈ C.A := C.A₀_le _ (C.ppt_mem f t r)
      have hA2 : C.ppt f t r0 ∈ C.A := C.A₀_le _ (C.ppt_mem f t r0)
      have l1 := FullTriple.L_lin (T := C.toFullTriple) hA1 hA2 (-1)
      filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨C.L ρ', C.Lm hρ'⟩,
        Lp.coeFn_sub (C.orb (C.Lt f) (t - r)) (C.orb (C.Lt f) (t - r0)),
        C.L_Pt f ((t : ℝ) - r), C.L_Pt f ((t : ℝ) - r0), l1] with w a1 a2 a3 a4 a5
      rw [a1, a2, Pi.sub_apply, ← a3, ← a4]
      have : C.L ρ' w = C.L (fun x => C.ppt f t r x + (-1) * C.ppt f t r0 x) w := rfl
      rw [this, a5]; simp only [ppt]; ring
    have hE : ∫ w, FullTriple.G C.toFullTriple ρ' ρ' w ∂C.μ ≤ e1 r * e2 r := by
      have := FullTriple.int_G_self_le (T := C.toFullTriple) hρ'
      rw [hcls, hLcls] at this
      exact this
    have hE0 := C.int_G_nonneg hρ'
    rw [hnorm]
    refine hrem.trans ?_
    simp only [zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul, add_zero, mul_zero, zero_pow two_ne_zero]
    nlinarith [hE, mul_nonneg hB0 hE0]
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun r => Real.sqrt (8 * B * (e1 r * e2 r))) (𝓝 r0) (𝓝 0) := by
    have h3 := (he1.mul he2).const_mul (8 * B)
    rw [zero_mul, mul_zero] at h3
    have := (Real.continuous_sqrt.tendsto 0).comp h3
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
  filter_upwards [hsq] with r hr
  exact Real.le_sqrt_of_sq_le hr

end CompactTriple

end MarkovTriple.BGL
