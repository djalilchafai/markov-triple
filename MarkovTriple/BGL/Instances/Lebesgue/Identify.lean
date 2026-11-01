import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Core
import MarkovTriple.BGL.Instances.Lebesgue.Heat

/-!
# The Friedrichs semigroup of the Brownian triple is Gaussian smoothing

For `f ∈ C_c^∞(ℝ)` and `t ≥ 0`: `P_t [f] = [heatM (√(2t)) f]` in `L²(ℝ)`.
Proof: Duhamel's argument `s ↦ ⟪P_s f, Q_{t-s} ψ⟫` is constant (strong derivative of `P_s f`
from the semigroup, strong derivative of the Gaussian smoothing from `Heat.lean`, and
`Q_r ψ ∈ 𝒟(L)`, `L Q_r ψ = Q_r ψ''` from the cutoff lemma).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

lemma isTest_of {f : ℝ → ℝ} (hf : f ∈ A₀) : IsTest f := hf

lemma inner_toLp {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

/-- symmetry of the generator. -/
lemma gen_symm {x y : Lp ℝ 2 (volume : Measure ℝ)} (hx : x ∈ lebesgueDiffusion.generator.domain)
    (hy : y ∈ lebesgueDiffusion.generator.domain) :
    inner ℝ (lebesgueDiffusion.generator ⟨x, hx⟩) y =
      inner ℝ x (lebesgueDiffusion.generator ⟨y, hy⟩) := by
  set S := DiffusionTriple.formData lebesgueDiffusion
  have hRx : S.R (x - lebesgueDiffusion.generator ⟨x, hx⟩) = x :=
    (S.generator_apply_eq_iff hx _).1 rfl
  have hRy : S.R (y - lebesgueDiffusion.generator ⟨y, hy⟩) = y :=
    (S.generator_apply_eq_iff hy _).1 rfl
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp S.R_isSelfAdjoint
    (x - lebesgueDiffusion.generator ⟨x, hx⟩) (y - lebesgueDiffusion.generator ⟨y, hy⟩)
  erw [hRx, hRy] at hs
  have e1 : lebesgueDiffusion.generator ⟨x, hx⟩ = x - (x - lebesgueDiffusion.generator ⟨x, hx⟩) := by abel
  have e2 : lebesgueDiffusion.generator ⟨y, hy⟩ = y - (y - lebesgueDiffusion.generator ⟨y, hy⟩) := by abel
  set g := x - lebesgueDiffusion.generator ⟨x, hx⟩
  set h := y - lebesgueDiffusion.generator ⟨y, hy⟩
  rw [e1, e2, inner_sub_left, inner_sub_right]
  rw [hs]

lemma heat_mem_domain {ψ : ℝ → ℝ} (hψ : IsTest ψ) (a : ℝ) :
    ∃ h : heatL2 hψ a ∈ lebesgueDiffusion.generator.domain,
      lebesgueDiffusion.generator ⟨heatL2 hψ a, h⟩ = heatL2 hψ.dtest.dtest a := by
  have e1 := hψ.deriv_heatM a
  have e2 : deriv (deriv (heatM a ψ)) = heatM a (deriv (deriv ψ)) := by
    rw [e1, hψ.dtest.deriv_heatM a]
  have h0 := hψ.memLp_heatM a
  have h1 : MemLp (deriv (heatM a ψ)) 2 volume := by rw [e1]; exact hψ.dtest.memLp_heatM a
  have h2 : MemLp (deriv (deriv (heatM a ψ))) 2 volume := by
    rw [e2]; exact hψ.dtest.dtest.memLp_heatM a
  obtain ⟨h, hG⟩ := domain_of_smooth_L2 (hψ.heatM_contDiff a) h0 h1 h2
  refine ⟨h, ?_⟩
  refine hG.trans ?_
  refine Lp.ext ?_
  filter_upwards [(hψ.dtest.dtest.memLp_heatM a).coeFn_toLp, h2.coeFn_toLp] with x p q
  rw [q]
  exact (congrArg (fun z => z x) e2).trans p.symm

lemma heatL2_zero {ψ : ℝ → ℝ} (hψ : ψ ∈ A₀) :
    heatL2 (isTest_of hψ) 0 = lebesgueDiffusion.cls ⟨ψ, hψ⟩ := by
  show (_ : MemLp (heatM 0 ψ) 2 volume).toLp (heatM 0 ψ) = _
  refine Lp.ext ?_
  filter_upwards [(IsTest.memLp_heatM (isTest_of hψ) 0).coeFn_toLp,
    lebesgueDiffusion.coeFn_cls ⟨ψ, hψ⟩] with x p q
  rw [p, q, heatM_zero]

/-- Pairing statement: `⟪P_t f, ψ⟫ = ⟪Q_t f, ψ⟫` for `t > 0`. -/
theorem inner_semigroup_heat {f : ℝ → ℝ} (hf : f ∈ A₀) {ψ : ℝ → ℝ} (hψ : ψ ∈ A₀) {t : ℝ}
    (ht : 0 < t) :
    inner ℝ (lebesgueDiffusion.semigroup t.toNNReal (lebesgueDiffusion.cls ⟨f, hf⟩))
      (lebesgueDiffusion.cls ⟨ψ, hψ⟩) =
    inner ℝ (heatL2 (isTest_of hf) (Real.sqrt (2 * t))) (lebesgueDiffusion.cls ⟨ψ, hψ⟩) := by
  set T := lebesgueDiffusion
  set S := DiffusionTriple.formData T with hS
  have hψT : IsTest ψ := isTest_of hψ
  have hfT : IsTest f := isTest_of hf
  set F : Lp ℝ 2 (volume : Measure ℝ) := T.cls ⟨f, hf⟩ with hF
  have hFd : F ∈ T.generator.domain := T.cls_mem_generator_domain ⟨f, hf⟩
  have hGF : T.generator ⟨F, hFd⟩ = T.Lcls ⟨f, hf⟩ := T.generator_cls ⟨f, hf⟩ hFd
  set g0 : Lp ℝ 2 (volume : Measure ℝ) := F - T.generator ⟨F, hFd⟩ with hg0
  have hRg0 : S.R g0 = F := (S.generator_apply_eq_iff hFd _).1 rfl
  set u : ℝ → Lp ℝ 2 (volume : Measure ℝ) := fun s => S.semigroup s.toNNReal F with hu
  set w : ℝ → Lp ℝ 2 (volume : Measure ℝ) := fun s => heatL2 hψT (Real.sqrt (2 * (t - s))) with hw
  set g : ℝ → ℝ := fun s => inner ℝ (u s) (w s) with hg
  have hucont : Continuous u :=
    (S.continuous_semigroup_apply F).comp continuous_real_toNNReal
  have hwcont : Continuous w := by
    have h1 : Continuous (heatL2 hψT) :=
      continuous_iff_continuousAt.2 fun a => (hψT.hasDerivAt_heatL2 a).continuousAt
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
    have hw' : HasDerivAt w (-(heatL2 hψT.dtest.dtest a)) s := by
      have h1 := (hψT.hasDerivAt_heatL2 a).scomp s hσ
      refine h1.congr_deriv ?_
      rw [smul_smul]
      have : (-1 / a) * a = -1 := by field_simp
      rw [this]; simp
    have hg' := hu'.inner ℝ hw'
    have hgd : g = fun s => inner ℝ (u s) (w s) := rfl
    rw [hgd]
    refine hg'.congr_deriv ?_
    obtain ⟨hwd, hGw⟩ := heat_mem_domain hψT a
    obtain ⟨hPd, hPG⟩ := S.semigroup_generator_comm hFd s.toNNReal
    have e1 : inner ℝ (S.semigroup s.toNNReal (T.generator ⟨F, hFd⟩)) (w s) =
        inner ℝ (S.semigroup s.toNNReal F) (heatL2 hψT.dtest.dtest a) := by
      have hPG' : S.semigroup s.toNNReal (T.generator ⟨F, hFd⟩) =
          T.generator ⟨S.semigroup s.toNNReal F, hPd⟩ := hPG.symm
      rw [hPG', show w s = heatL2 hψT a from rfl]
      have := gen_symm hPd hwd
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
    rw [heatL2_zero hψ]
  have hg0' : g 0 = inner ℝ (heatL2 hfT (Real.sqrt (2 * t))) (T.cls ⟨ψ, hψ⟩) := by
    simp only [hg, hu, hw, sub_zero, Real.toNNReal_zero, S.semigroup_zero]
    show inner ℝ F (heatL2 hψT (Real.sqrt (2 * t))) = inner ℝ (heatL2 hfT (Real.sqrt (2 * t))) _
    show inner ℝ ((memLp_of hf 2).toLp f) ((hψT.memLp_heatM _).toLp _) =
      inner ℝ ((hfT.memLp_heatM _).toLp _) ((memLp_of hψ 2).toLp ψ)
    rw [inner_toLp, inner_toLp, ← hfT.integral_mul_heatM_comm hψT]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  exact (hgt.symm.trans (hg0.symm.trans hg0'))

end MarkovTriple.BGL.Lebesgue
