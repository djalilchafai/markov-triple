import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Esa
import MarkovTriple.BGL.Instances.LebesgueRd.Full.DomainAPI
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Semigroup.Characterization

/-!
# The Friedrichs semigroup of `(ℝ^d, Lebesgue)` is Gaussian smoothing (Round 24, stream A, part B-b)

For `f ∈ C_c^∞(ℝ^d)` and `t ≥ 0`: `P_t [f] = heatL2 f (√(2t))` in `L²(ℝ^d)`.  Duhamel's argument
`s ↦ ⟪P_s f, Q_{t-s} ψ⟫` is constant; verbatim port of `Instances/Lebesgue/Identify.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL.LebesgueRd

open MarkovTriple.BGL

variable {d : ℕ}

lemma inner_toLp' {f g : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

/-- symmetry of the generator. -/
lemma gen_symm' (hd : 1 ≤ d) {x y : Lp ℝ 2 (volume : Measure (Fin d → ℝ))}
    (hx : x ∈ (lebesgueRdDiffusion d hd).generator.domain)
    (hy : y ∈ (lebesgueRdDiffusion d hd).generator.domain) :
    inner ℝ ((lebesgueRdDiffusion d hd).generator ⟨x, hx⟩) y =
      inner ℝ x ((lebesgueRdDiffusion d hd).generator ⟨y, hy⟩) := by
  set S := DiffusionTriple.formData (lebesgueRdDiffusion d hd)
  have hRx : S.R (x - (lebesgueRdDiffusion d hd).generator ⟨x, hx⟩) = x :=
    (S.generator_apply_eq_iff hx _).1 rfl
  have hRy : S.R (y - (lebesgueRdDiffusion d hd).generator ⟨y, hy⟩) = y :=
    (S.generator_apply_eq_iff hy _).1 rfl
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp S.R_isSelfAdjoint
    (x - (lebesgueRdDiffusion d hd).generator ⟨x, hx⟩) (y - (lebesgueRdDiffusion d hd).generator ⟨y, hy⟩)
  erw [hRx, hRy] at hs
  have e1 : (lebesgueRdDiffusion d hd).generator ⟨x, hx⟩ =
      x - (x - (lebesgueRdDiffusion d hd).generator ⟨x, hx⟩) := by abel
  have e2 : (lebesgueRdDiffusion d hd).generator ⟨y, hy⟩ =
      y - (y - (lebesgueRdDiffusion d hd).generator ⟨y, hy⟩) := by abel
  set g := x - (lebesgueRdDiffusion d hd).generator ⟨x, hx⟩
  set h := y - (lebesgueRdDiffusion d hd).generator ⟨y, hy⟩
  rw [e1, e2, inner_sub_left, inner_sub_right]
  rw [hs]

/-- Pairing statement: `⟪P_t f, ψ⟫ = ⟪Q_t f, ψ⟫` for `t > 0`. -/
theorem inner_semigroup_heatRd (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d)
    {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ A₀ d) {t : ℝ} (ht : 0 < t) :
    inner ℝ ((lebesgueRdDiffusion d hd).semigroup t.toNNReal ((lebesgueRdDiffusion d hd).cls ⟨f, hf⟩))
      ((lebesgueRdDiffusion d hd).cls ⟨ψ, hψ⟩) =
    inner ℝ (heatL2 f (Real.sqrt (2 * t))) ((lebesgueRdDiffusion d hd).cls ⟨ψ, hψ⟩) := by
  set T := lebesgueRdDiffusion d hd
  set S := DiffusionTriple.formData T with hS
  set F : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) := T.cls ⟨f, hf⟩ with hF
  have hFd : F ∈ T.generator.domain := T.cls_mem_generator_domain ⟨f, hf⟩
  have hGF : T.generator ⟨F, hFd⟩ = T.Lcls ⟨f, hf⟩ := T.generator_cls ⟨f, hf⟩ hFd
  set g0 : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) := F - T.generator ⟨F, hFd⟩ with hg0
  have hRg0 : S.R g0 = F := (S.generator_apply_eq_iff hFd _).1 rfl
  set u : ℝ → Lp ℝ 2 (volume : Measure (Fin d → ℝ)) := fun s => S.semigroup s.toNNReal F with hu
  set w : ℝ → Lp ℝ 2 (volume : Measure (Fin d → ℝ)) := fun s => heatL2 ψ (Real.sqrt (2 * (t - s)))
    with hw
  set g : ℝ → ℝ := fun s => inner ℝ (u s) (w s) with hg
  have hucont : Continuous u :=
    (S.continuous_semigroup_apply F).comp continuous_real_toNNReal
  have hwcont : Continuous w := by
    have h1 : Continuous (heatL2 ψ : ℝ → Lp ℝ 2 (volume : Measure (Fin d → ℝ))) :=
      continuous_iff_continuousAt.2 fun a => (hasDerivAt_heatL2 hψ a).continuousAt
    exact h1.comp (by fun_prop)
  have hgcont : Continuous g := hucont.inner hwcont
  have hderiv : ∀ s, 0 < s → s < t → HasDerivAt g 0 s := by
    intro s hs0 hst
    have hu' : HasDerivAt u (S.semigroup s.toNNReal (T.generator ⟨F, hFd⟩)) s := by
      have h1 := S.hasDerivAt_semigroup hs0 g0
      rw [hRg0] at h1
      refine h1.congr_deriv ?_
      have : g0 - F = -T.generator ⟨F, hFd⟩ := by rw [hg0]; abel
      rw [this, map_neg, neg_neg]
    set a : ℝ := Real.sqrt (2 * (t - s)) with ha
    have hapos : 0 < a := Real.sqrt_pos.2 (by linarith)
    have hσ : HasDerivAt (fun y : ℝ => Real.sqrt (2 * (t - y))) (-1 / a) s := by
      have h1 : HasDerivAt (fun y : ℝ => 2 * (t - y)) (-2) s := by
        simpa using ((hasDerivAt_id s).const_sub t).const_mul 2
      have h2 := h1.sqrt (by linarith)
      refine h2.congr_deriv ?_
      rw [← ha]; field_simp
    have hw' : HasDerivAt w (-(heatL2 (Lf ψ) a)) s := by
      have h1 := (hasDerivAt_heatL2 hψ a).scomp s hσ
      refine h1.congr_deriv ?_
      rw [smul_smul]
      have : (-1 / a) * a = -1 := by field_simp
      rw [this]; simp
    have hg' := hu'.inner ℝ hw'
    have hgd : g = fun s => inner ℝ (u s) (w s) := rfl
    rw [hgd]
    refine hg'.congr_deriv ?_
    obtain ⟨hwd, hGw⟩ := heatL2_mem_domain hd hψ a
    obtain ⟨hPd, hPG⟩ := S.semigroup_generator_comm hFd s.toNNReal
    have e1 : inner ℝ (S.semigroup s.toNNReal (T.generator ⟨F, hFd⟩)) (w s) =
        inner ℝ (S.semigroup s.toNNReal F) (heatL2 (Lf ψ) a) := by
      have hPG' : S.semigroup s.toNNReal (T.generator ⟨F, hFd⟩) =
          T.generator ⟨S.semigroup s.toNNReal F, hPd⟩ := hPG.symm
      rw [hPG', show w s = heatL2 ψ a from rfl]
      have := gen_symm' hd hPd hwd
      rw [this, hGw]
    rw [e1]
    simp only [inner_neg_right]
    ring
  -- constancy
  have hconst : ∀ ε, 0 < ε → ε < t → g ε = g t := by
    intro ε hε hεt
    have := constant_of_has_deriv_right_zero (f := g) (a := ε) (b := t)
      hgcont.continuousOn
      (fun x hx => (hderiv x (lt_of_lt_of_le hε hx.1) hx.2).hasDerivWithinAt) t
      ⟨hεt.le, le_rfl⟩
    exact this.symm
  have hg0 : g 0 = g t := by
    have h1 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
      hgcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g t)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [Ioo_mem_nhdsGT ht] with s hs
        exact (hconst s hs.1 hs.2).symm)
    exact tendsto_nhds_unique h1 h2
  -- endpoints
  have hgt : g t = inner ℝ (S.semigroup t.toNNReal F) (T.cls ⟨ψ, hψ⟩) := by
    simp only [hg, hu, hw, sub_self, mul_zero, Real.sqrt_zero]
    rw [heatL2_zero hψ]; rfl
  have hg0' : g 0 = inner ℝ (heatL2 f (Real.sqrt (2 * t))) (T.cls ⟨ψ, hψ⟩) := by
    simp only [hg, hu, hw, sub_zero, Real.toNNReal_zero, S.semigroup_zero]
    show inner ℝ F (heatL2 ψ (Real.sqrt (2 * t))) = inner ℝ (heatL2 f (Real.sqrt (2 * t))) _
    rw [heatL2_eq hf, heatL2_eq hψ]
    show inner ℝ ((memLp_of hf 2).toLp f) ((memLp_heatRd hψ _).toLp _) =
      inner ℝ ((memLp_heatRd hf _).toLp _) ((memLp_of hψ 2).toLp ψ)
    rw [inner_toLp', inner_toLp', ← integral_mul_heatRd_comm hf hψ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  exact (hgt.symm.trans (hg0.symm.trans hg0'))

/-- **Identification of the Friedrichs semigroup with Gaussian smoothing.** -/
theorem semigroup_eq_heatRd (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) (t : ℝ≥0) :
    (lebesgueRdDiffusion d hd).semigroup t ((lebesgueRdDiffusion d hd).cls ⟨f, hf⟩) =
      heatL2 f (Real.sqrt (2 * t)) := by
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h0 | hpos
  · subst h0
    have : DiffusionTriple.semigroup (lebesgueRdDiffusion d hd) 0 = 1 :=
      (DiffusionTriple.formData (lebesgueRdDiffusion d hd)).semigroup_zero
    rw [this]
    simp only [one_apply_eq_self, NNReal.coe_zero, mul_zero, Real.sqrt_zero]
    rw [heatL2_zero hf]; rfl
  · rw [← sub_eq_zero]
    refine (lebesgueRdDiffusion d hd).eq_zero_of_orth _ (fun g => ?_)
    rw [inner_sub_left, sub_eq_zero]
    have := inner_semigroup_heatRd hd hf g.2 (t := (t : ℝ)) (by exact_mod_cast hpos)
    rw [Real.toNNReal_coe] at this
    exact this

end MarkovTriple.BGL.LebesgueRd
