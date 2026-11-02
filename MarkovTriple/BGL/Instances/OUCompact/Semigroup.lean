import Mathlib
import MarkovTriple.BGL.Instances.OUCompact.Diffusion
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Analysis.OU.MehlerEq
import MarkovTriple.BGL.Analysis.OU.Ergodic

/-!
# The Friedrichs semigroup of the triple `(ℝ, γ, ℬ)`: Mehler, `ℬ`-invariance, ESA, S10, S11

For the BGL semigroup `ouB.semigroup` (Friedrichs extension of `L|ℬ`):

* the Hermite functions are eigenfunctions (`Pt_hL`), since `C_c^∞ ⊂ ℬ` (`Pt_gen`);
* Mehler's formula `P_t[f] = Mh e^{-t} √(1-e^{-2t}) f` holds for every `f ∈ ℬ`
  (`Pt_mehler`; the Hermite-coefficient computation only needs `f` continuous and bounded);
* hence `P_t` maps `[ℬ]` into `[ℬ]` (`semigroup_invariant`; `Bm.Mh`), and `ℬ` is a core
  (`ouB_esa`, via `DiffusionTriple.core_of_invariant`);
* S10 (ergodicity: from ESA and the Hermite basis) and S11 (`P_t 1 = 1`: `1 = h₀`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Polynomial
open scoped ENNReal NNReal Real InnerProductSpace LinearPMap SchwartzMap
open MarkovTriple.Sanity.OU hiding A₀
open MarkovTriple.Sanity.Circle (IsSG)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OUCompact

/-- the Friedrichs semigroup of the triple `ouB`, on `L²(γ)` -/
noncomputable abbrev PtB : ℝ≥0 → (Lp ℝ 2 ouB.μ →L[ℝ] Lp ℝ 2 ouB.μ) := ouB.semigroup

lemma PtB_IsSG : IsSG PtB where
  zero := (DiffusionTriple.formData ouB).semigroup_zero
  add := fun s t => (DiffusionTriple.formData ouB).semigroup_add s t
  cont := fun u => by
    have h : Tendsto (fun t : ℝ≥0 => PtB t u) (𝓝 0) (𝓝 (PtB 0 u)) :=
      ((DiffusionTriple.formData ouB).continuous_semigroup_apply u).tendsto 0
    have h0 : PtB 0 u = u := by
      have := (DiffusionTriple.formData ouB).semigroup_zero
      exact congrArg (fun T => T u) this
    rw [h0] at h
    exact h

lemma PtB_gen : GenA₀ PtB := by
  intro g hg u v hu hv
  have hgB : g ∈ ouB.A₀ := bm_of_cs hg.1 hg.2
  have hmem : ouB.cls ⟨g, hgB⟩ ∈ ouB.generator.domain :=
    DiffusionTriple.cls_mem_generator_domain ouB ⟨g, hgB⟩
  have hG := DiffusionTriple.generator_cls ouB ⟨g, hgB⟩ hmem
  have hu' : u = ouB.cls ⟨g, hgB⟩ :=
    Lp.ext (hu.trans (DiffusionTriple.coeFn_cls ouB ⟨g, hgB⟩).symm)
  have hv' : v = ouB.Lcls ⟨g, hgB⟩ :=
    Lp.ext (hv.trans (DiffusionTriple.coeFn_Lcls ouB ⟨g, hgB⟩).symm)
  subst hu' hv'
  exact ((DiffusionTriple.formData ouB).tendsto_generator_iff _ _).1 ⟨hmem, hG⟩

/-- Hermite functions are eigenfunctions of the Friedrichs semigroup: `P_t h_n = e^{-nt} h_n`. -/
theorem PtB_hL (n : ℕ) (t : ℝ≥0) : PtB t (hL n) = Real.exp (-(n : ℝ) * t) • hL n :=
  eigen_hL PtB_IsSG PtB_gen n t

/-! ### Mehler's formula for `f ∈ ℬ` -/

/-- Hermite coefficients of the Mehler transform (generalised from `coeff_Mh` to `f ∈ ℬ`). -/
lemma coeff_Mh_bm {a c : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hc : c = √(1 - a ^ 2)) {f : ℝ → ℝ}
    (hf : Bm f) (n : ℕ) :
    ∫ x, hh n x * Mh a c f x ∂γ = a ^ n * ∫ x, hh n x * f x ∂γ := by
  have hac : a ^ 2 + c ^ 2 = 1 := by rw [hc, Real.sq_sqrt (by nlinarith)]; ring
  obtain ⟨B, hB⟩ := hf.bdd
  set θ := Real.arccos a
  have hcos : Real.cos θ = a := Real.cos_arccos (by linarith) ha1
  have hsin : Real.sin θ = c := by rw [Real.sin_arccos, hc]
  set R : ℝ × ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.rotation θ with hRdef
  have hR : ∀ p : ℝ × ℝ, R p = (a * p.1 + c * p.2, -c * p.1 + a * p.2) := by
    intro p; simp [hRdef, ContinuousLinearMap.rotation_apply, hcos, hsin]
  have hmap : (γ.prod γ).map R = γ.prod γ :=
    IsGaussian.map_rotation_eq_self (by simp [integral_id_gaussianReal]) θ
  set G : ℝ × ℝ → ℝ := fun p => hh n (a * p.1 - c * p.2) * f p.1 with hG
  set F : ℝ × ℝ → ℝ := fun p => hh n p.1 * f (a * p.1 + c * p.2) with hF
  have hGR : ∀ p : ℝ × ℝ, G (R p) = F p := by
    intro p
    simp only [hG, hF, hR]
    have : a * (a * p.1 + c * p.2) - c * (-c * p.1 + a * p.2) = p.1 := by
      linear_combination p.1 * hac
    rw [this]
  have hFm : AEStronglyMeasurable F (γ.prod γ) :=
    (((hh_sm n).continuous.comp continuous_fst).mul
      (hf.sm.continuous.comp (by fun_prop))).aestronglyMeasurable
  have hFint : Integrable F (γ.prod γ) := by
    have h1 : Integrable (fun p : ℝ × ℝ => B * |hh n p.1|) (γ.prod γ) :=
      (((hh_PG n).integrable.abs).comp_fst γ).const_mul B
    refine h1.mono' hFm (ae_of_all _ fun p => ?_)
    simp only [hF, norm_mul, Real.norm_eq_abs]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _) |>.trans_eq (by ring) |>.trans_eq rfl
  have hGm : AEStronglyMeasurable G (γ.prod γ) :=
    (((hh_sm n).continuous.comp (by fun_prop)).mul
      (hf.sm.continuous.comp continuous_fst)).aestronglyMeasurable
  have hRm : AEMeasurable R (γ.prod γ) := R.continuous.measurable.aemeasurable
  have hGint : Integrable G (γ.prod γ) := by
    have : Integrable G ((γ.prod γ).map R) := by
      rw [integrable_map_measure (by rwa [hmap]) hRm]
      have : G ∘ R = F := funext hGR
      rw [this]; exact hFint
    rwa [hmap] at this
  have hinner : ∀ z, ∫ w, G (z, w) ∂γ = f z * (a ^ n * hh n z) := by
    intro z
    have h1 : ∀ w, G (z, w) = f z * ((√(n.factorial : ℝ))⁻¹ *
        (He n).eval (a * z + (-c) * w)) := by
      intro w; simp only [hG, hh]; ring_nf
    simp_rw [h1]
    rw [integral_const_mul, integral_const_mul,
      (Q_eq a (-c) (by nlinarith) n).1 z]
    simp only [hh]; ring
  calc ∫ x, hh n x * Mh a c f x ∂γ = ∫ x, ∫ y, hh n x * f (a * x + c * y) ∂γ ∂γ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [Mh]; rw [integral_const_mul]
    _ = ∫ p, F p ∂(γ.prod γ) := (integral_prod F hFint).symm
    _ = ∫ p, G (R p) ∂(γ.prod γ) := by simp_rw [hGR]
    _ = ∫ p, G p ∂(γ.prod γ) := by
        rw [← integral_map hRm (by rwa [hmap]), hmap]
    _ = ∫ z, ∫ w, G (z, w) ∂γ ∂γ := integral_prod G hGint
    _ = ∫ z, a ^ n * (hh n z * f z) ∂γ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        dsimp only
        rw [hinner]; ring
    _ = _ := integral_const_mul _ _

/-- **Mehler's formula** for any semigroup with the Hermite eigenfunctions, for `f ∈ ℬ`. -/
theorem mehler_of_sg_bm {P : ℝ≥0 → (Lp ℝ 2 γ →L[ℝ] Lp ℝ 2 γ)} (hsg : IsSG P) (hgenA : GenA₀ P)
    (hself' : ∀ (t : ℝ≥0) (u v : Lp ℝ 2 γ), ⟪P t u, v⟫_ℝ = ⟪u, P t v⟫_ℝ)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Bm f) (u : Lp ℝ 2 γ) (hu : (u : ℝ → ℝ) =ᵐ[γ] f) :
    ((P t u : Lp ℝ 2 γ) : ℝ → ℝ) =ᵐ[γ]
      Mh (Real.exp (-(t : ℝ))) (√(1 - Real.exp (-(t : ℝ)) ^ 2)) f := by
  set a := Real.exp (-(t : ℝ)) with ha
  set c := √(1 - a ^ 2) with hc
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by rw [ha]; exact Real.exp_le_one_iff.2 (by simp)
  have hc1 : |c| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.2 (by nlinarith)
  have hMm : MemLp (Mh a c f) 2 γ := (Bm.Mh ha0 c hc1 hf).memLp 2
  have hz : P t u - hMm.toLp (Mh a c f) = 0 := by
    refine eq_zero_of_orth_hL fun n => ?_
    rw [inner_sub_right]
    have e1 : ⟪hL n, P t u⟫_ℝ = a ^ n * ∫ x, hh n x * f x ∂γ := by
      refine (hself' t (hL n) u).symm.trans ?_
      rw [eigen_hL hsg hgenA n t, inner_smul_left, inner_hL]
      have : Real.exp (-(n : ℝ) * t) = a ^ n := by
        rw [ha, ← Real.exp_nat_mul]; ring_nf
      simp only [RCLike.conj_to_real, this]
      congr 1
      exact integral_congr_ae (hu.mono fun x hx => by simp only [hx])
    have e2 : ⟪hL n, hMm.toLp (Mh a c f)⟫_ℝ = a ^ n * ∫ x, hh n x * f x ∂γ := by
      rw [inner_hL, ← coeff_Mh_bm ha0 ha1 hc hf n]
      exact integral_congr_ae (hMm.coeFn_toLp.mono fun x hx => by simp only [hx])
    rw [e1, e2, sub_self]
  have := sub_eq_zero.1 hz
  rw [this]
  exact hMm.coeFn_toLp

/-- **Mehler's formula for the BGL (Friedrichs) semigroup of `(ℝ, γ, ℬ)`**. -/
theorem PtB_mehler (t : ℝ≥0) {f : ℝ → ℝ} (hf : Bm f) (u : Lp ℝ 2 ouB.μ)
    (hu : (u : ℝ → ℝ) =ᵐ[γ] f) :
    ((PtB t u : Lp ℝ 2 ouB.μ) : ℝ → ℝ) =ᵐ[γ]
      Mh (Real.exp (-(t : ℝ))) (√(1 - Real.exp (-(t : ℝ)) ^ 2)) f :=
  mehler_of_sg_bm (P := PtB) PtB_IsSG PtB_gen
    (fun t u v => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((DiffusionTriple.formData ouB).semigroup_isSelfAdjoint t) u v) t hf u hu

/-! ### F8 and F10 -/

/-- `P_t` maps classes of test functions to classes of functions in `ℬ` (F8). -/
theorem semigroup_cls_mem (t : ℝ≥0) (f : ouB.A₀) :
    ∃ g ∈ Bfull, (ouB.semigroup t (ouB.cls f) : ℝ → ℝ) =ᵐ[ouB.μ] g := by
  set a := Real.exp (-(t : ℝ)) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by rw [ha]; exact Real.exp_le_one_iff.2 (by simp)
  have hc1 : |√(1 - a ^ 2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.2 (by nlinarith)
  refine ⟨Mh a (√(1 - a ^ 2)) f.1, Bm.Mh ha0 _ hc1 f.2, ?_⟩
  exact PtB_mehler t f.2 (ouB.cls f) (DiffusionTriple.coeFn_cls ouB f)

theorem semigroup_invariant (t : ℝ≥0) (f : ouB.A₀) :
    ∃ g : ouB.A₀, ouB.semigroup t (ouB.cls f) = ouB.cls g := by
  obtain ⟨g, hg, hae⟩ := semigroup_cls_mem t f
  exact ⟨⟨g, hg⟩, Lp.ext (hae.trans (DiffusionTriple.coeFn_cls ouB ⟨g, hg⟩).symm)⟩

/-- **ESA (F10)**: `ℬ` is a core for the Friedrichs generator. -/
theorem ouB_esa (u : Lp ℝ 2 ouB.μ) (hu : u ∈ ouB.generator.domain) :
    ∃ a : ℕ → ouB.A₀, Tendsto (fun n => ouB.cls (a n)) atTop (𝓝 u) ∧
      Tendsto (fun n => ouB.Lcls (a n)) atTop (𝓝 (ouB.generator ⟨u, hu⟩)) :=
  DiffusionTriple.core_of_invariant ouB semigroup_invariant u hu

/-! ### S10: ergodicity -/

lemma tendsto_eLpNorm_of_Lp' {v : ℕ → Lp ℝ 2 ouB.μ} {w : Lp ℝ 2 ouB.μ} {F : ℕ → ℝ → ℝ} {W : ℝ → ℝ}
    (hv : Tendsto v atTop (𝓝 w)) (hF : ∀ n, (v n : ℝ → ℝ) =ᵐ[γ] F n) (hW : (w : ℝ → ℝ) =ᵐ[γ] W) :
    Tendsto (fun n => eLpNorm (F n - W) 2 γ) atTop (𝓝 0) := by
  have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' v w).1 hv
  refine this.congr fun n => ?_
  exact eLpNorm_congr_ae ((hF n).sub hW)

lemma pg_deriv_hh (m : ℕ) : PG (deriv (hh m)) := by
  rcases m with _ | m
  · have : deriv (hh 0) = fun _ => 0 := funext hh_zero_deriv
    rw [this]; exact pg_const 0
  · have : deriv (hh (m + 1)) = fun x => √((m : ℝ) + 1) * hh m x := funext (hh_succ_deriv m)
    rw [this]; exact (hh_PG m).const_mul _

lemma integrable_pg_mul_bm {F g : ℝ → ℝ} (hF : PG F) (hg : Bm g) :
    Integrable (fun x => g x * F x) γ := by
  obtain ⟨C, hC⟩ := hg.bdd
  exact ((pg_bounded hg.sm.continuous ⟨C, hC⟩).mul hF).integrable

lemma integrable_pg_mul_bm' {F g : ℝ → ℝ} (hF : PG F) (hg : Bm g) :
    Integrable (fun x => F x * g x) γ :=
  (integrable_pg_mul_bm hF hg).congr (ae_of_all _ fun _x => mul_comm _ _)

lemma ibp_hh_bm {g : ℝ → ℝ} (hg : Bm g) (m : ℕ) :
    ∫ x, g x * Lo (hh m) x ∂γ = ∫ x, hh m x * Lo g x ∂γ := by
  have hPG1 : PG (Lo (hh m)) := by rw [Lo_hh]; exact (hh_PG m).const_mul _
  have hPGd := pg_deriv_hh m
  have h1 := ibp_master (hh_sm m) hg.sm (integrable_pg_mul_bm hPG1 hg)
    (integrable_pg_mul_bm hPGd hg.deriv_bm) (integrable_pg_mul_bm hPGd hg)
  have h2 := ibp_master hg.sm (hh_sm m) (integrable_pg_mul_bm' (hh_PG m) (bm_Lo hg))
    (integrable_pg_mul_bm' hPGd hg.deriv_bm) (integrable_pg_mul_bm' (hh_PG m) hg.deriv_bm)
  rw [h1, h2]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- Ergodicity from approximation by test functions (the legacy `ou_ergodic_aux` for `ℬ`). -/
theorem ergodic_aux_bm : ∀ u : Lp ℝ 2 γ,
    (∃ f : ℕ → ℝ → ℝ, (∀ n, Bm (f n)) ∧
      Tendsto (fun n => eLpNorm (f n - (u : ℝ → ℝ)) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (Lo (f n)) 2 γ) atTop (𝓝 0)) →
    ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[γ] fun _ => c := by
  intro u ⟨f, hf, h1, h2⟩
  have horth : ∀ m : ℕ, 1 ≤ m → ⟪hL m, u⟫_ℝ = 0 := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    set uf : ℕ → Lp ℝ 2 γ := fun n => ((hf n).memLp 2).toLp (f n) with huf
    have hlim : Tendsto uf atTop (𝓝 u) := by
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      refine h1.congr fun n => ?_
      exact eLpNorm_congr_ae
        (((((hf n).memLp 2).coeFn_toLp).sub (EventuallyEq.refl _ _)).symm)
    have ha : Tendsto (fun n => ⟪hL m, uf n⟫_ℝ) atTop (𝓝 ⟪hL m, u⟫_ℝ) :=
      ((continuous_const.inner continuous_id).tendsto u).comp hlim
    set vL : ℕ → Lp ℝ 2 γ := fun n => ((bm_Lo (hf n)).memLp 2).toLp (Lo (f n)) with hvL
    have hv0 : Tendsto (fun n => ‖vL n‖) atTop (𝓝 0) := by
      have : ∀ n, ‖vL n‖ = (eLpNorm (Lo (f n)) 2 γ).toReal := fun n => by
        simp [hvL, Lp.norm_toLp]
      simp_rw [this]
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
      simpa [Function.comp_def] using this
    have heq : ∀ n, ⟪hL m, uf n⟫_ℝ = -(1 / (m : ℝ)) * ⟪hL m, vL n⟫_ℝ := by
      intro n
      rw [huf, hvL]
      simp only []
      rw [hL, inner_toLp, inner_toLp]
      have := ibp_hh_bm (hf n) m
      rw [Lo_hh] at this
      have e : ∫ x, hh m x * f n x ∂γ = -(1 / (m : ℝ)) * ∫ x, f n x * (-(m : ℝ) * hh m x) ∂γ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        field_simp
      rw [e, this]
    have hb : Tendsto (fun n => ⟪hL m, uf n⟫_ℝ) atTop (𝓝 0) := by
      have hn : ∀ n, |⟪hL m, uf n⟫_ℝ| ≤ (1 / (m : ℝ)) * (‖hL m‖ * ‖vL n‖) := by
        intro n
        rw [heq n, abs_mul, abs_neg, abs_of_pos (by positivity)]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
      have hz : Tendsto (fun n => (1 / (m : ℝ)) * (‖hL m‖ * ‖vL n‖)) atTop (𝓝 0) := by
        simpa using (hv0.const_mul ‖hL m‖).const_mul (1 / (m : ℝ))
      exact squeeze_zero_norm (fun n => by simpa using hn n) hz
    exact tendsto_nhds_unique ha hb
  set c : ℝ := ⟪hL 0, u⟫_ℝ with hc
  refine ⟨c, ?_⟩
  have hw : u - c • hL 0 = 0 := by
    refine eq_zero_of_orth_hL fun n => ?_
    rw [inner_sub_right, inner_smul_right]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hc, real_inner_self_eq_norm_sq, orthonormal_hL.1 0]; simp
    · rw [horth n hn, orthonormal_hL.inner_eq_zero (by omega : n ≠ 0)]; simp
  have hae : (u : ℝ → ℝ) =ᵐ[γ] ⇑(c • hL 0) := by
    have := congrArg (fun w : Lp ℝ 2 γ => (w : ℝ → ℝ)) (sub_eq_zero.1 hw)
    exact Filter.EventuallyEq.of_eq (by simpa using this) |> fun h => h
  filter_upwards [hae, Lp.coeFn_smul c (hL 0), (hh_memLp 0).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, hL, h3, hh_zero]; simp

/-- **S10**: `u ∈ 𝒟(L)`, `L u = 0` ⇒ `u` is a.e. constant. -/
theorem ouB_ergodic (u : Lp ℝ 2 ouB.μ) (hu : u ∈ ouB.generator.domain)
    (h0 : ouB.generator ⟨u, hu⟩ = 0) : ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[γ] fun _ => c := by
  obtain ⟨a, ha1, ha2⟩ := ouB_esa u hu
  rw [h0] at ha2
  refine ergodic_aux_bm u ⟨fun n => (a n).1, fun n => (a n).2, ?_, ?_⟩
  · exact tendsto_eLpNorm_of_Lp' ha1 (fun n => DiffusionTriple.coeFn_cls ouB (a n))
      (EventuallyEq.refl _ _)
  · have := tendsto_eLpNorm_of_Lp' (F := fun n => Lo (a n).1) (W := 0) ha2
      (fun n => DiffusionTriple.coeFn_Lcls ouB (a n)) (Lp.coeFn_zero ℝ 2 γ)
    simpa only [sub_zero] using this

/-! ### S11: conservativeness -/

lemma one2_eq_hL : ouB.one2 = hL 0 := by
  refine Lp.ext ?_
  filter_upwards [ouB.coeFn_one2, (hh_memLp 0).coeFn_toLp] with x h1 h2
  calc _ = (1 : ℝ) := h1
    _ = hh 0 x := by rw [hh_zero]
    _ = _ := h2.symm

/-- `P_t 1 = 1` in `L²(γ)`: `1 = h_0` is the eigenfunction for the eigenvalue `0`. -/
theorem PtB_one (t : ℝ≥0) : ouB.semigroup t ouB.one2 = ouB.one2 := by
  rw [one2_eq_hL]
  have := PtB_hL 0 t
  simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, one_smul] at this
  exact this

/-- **S11**: for every exhaustion sequence, `P_t u_n → 1` a.e. -/
theorem ouB_conservative {u : ℕ → ℝ → ℝ} (hu : IsExhaustion ouB.μ ouB.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂ouB.μ, Tendsto (fun n => (ouB.semigroup t
      (ouB.cls ⟨u n, hu.1 n⟩) : ℝ → ℝ) x) atTop (𝓝 1) :=
  ouB.conservative_of_semigroup_one hu t (PtB_one t)

end MarkovTriple.BGL.Instances.OUCompact
