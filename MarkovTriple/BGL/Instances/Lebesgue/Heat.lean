import Mathlib

/-!
# Gaussian smoothing on `ℝ` (heat flow) — analytic facts for the Lebesgue instance

`heatM a φ (x) = E φ(x - a Z)`, `Z ~ N(0,1)`; the heat semigroup at time `t` is `heatM (√(2t))`.
Everything here is about test functions `φ ∈ C_c^∞(ℝ)` (`IsTest`).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace MarkovTriple.BGL.Lebesgue

/-- test functions: `C_c^∞(ℝ)`. -/
def IsTest (φ : ℝ → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

/-- Gaussian smoothing `E φ(x - a Z)`. -/
noncomputable def heatM (a : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, φ (x - a * z) ∂(gaussianReal 0 1)

theorem heatM_zero (φ : ℝ → ℝ) : heatM 0 φ = φ := by
  funext x
  simp [heatM]

theorem IsTest.dtest {φ : ℝ → ℝ} (hφ : IsTest φ) : IsTest (deriv φ) := by
  refine ⟨(contDiff_infty_iff_deriv.1 hφ.1).2, hφ.2.deriv⟩

theorem IsTest.cont {φ : ℝ → ℝ} (hφ : IsTest φ) : Continuous φ := hφ.1.continuous

theorem IsTest.diff {φ : ℝ → ℝ} (hφ : IsTest φ) : Differentiable ℝ φ :=
  (contDiff_infty_iff_deriv.1 hφ.1).1

theorem IsTest.bdd {φ : ℝ → ℝ} (hφ : IsTest φ) : ∃ C, 0 ≤ C ∧ ∀ x, |φ x| ≤ C := by
  obtain ⟨C, hC⟩ := hφ.cont.bounded_above_of_compact_support hφ.2
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

lemma integrable_comp_gauss {φ : ℝ → ℝ} (hc : Continuous φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C)
    (a x : ℝ) : Integrable (fun z => φ (x - a * z)) (gaussianReal 0 1) :=
  Integrable.of_bound (C := C) (hc.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa using hC _)

lemma hasDerivAt_heatM {φ : ℝ → ℝ} (hd : Differentiable ℝ φ) (hc : Continuous φ)
    (hc' : Continuous (deriv φ)) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) {C' : ℝ}
    (hC' : ∀ x, |deriv φ x| ≤ C') (a x : ℝ) :
    HasDerivAt (heatM a φ) (heatM a (deriv φ) x) x := by
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun x z => φ (x - a * z)) (F' := fun x z => deriv φ (x - a * z)) (x₀ := x)
    (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun y => (hc.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_gauss hc hC a x) (hc'.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z y _ => by simpa using hC' _) (integrable_const C')
    (ae_of_all _ fun z y _ => ?_)).2
  · exact this
  · exact ((hd (y - a * z)).hasDerivAt).comp_sub_const y (a * z)

theorem IsTest.deriv_heatM {φ : ℝ → ℝ} (hφ : IsTest φ) (a : ℝ) :
    deriv (heatM a φ) = heatM a (deriv φ) := by
  obtain ⟨C, -, hC⟩ := hφ.bdd
  obtain ⟨C', -, hC'⟩ := hφ.dtest.bdd
  funext x
  exact (hasDerivAt_heatM hφ.diff hφ.cont hφ.dtest.cont hC hC' a x).deriv

theorem IsTest.heatM_contDiff {φ : ℝ → ℝ} (hφ : IsTest φ) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (heatM a φ) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing φ with
  | zero =>
    obtain ⟨C, -, hC⟩ := hφ.bdd
    obtain ⟨C', -, hC'⟩ := hφ.dtest.bdd
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_heatM hφ.diff hφ.cont hφ.dtest.cont hC hC' a x).continuousAt)
  | succ n ih =>
    obtain ⟨C, -, hC⟩ := hφ.bdd
    obtain ⟨C', -, hC'⟩ := hφ.dtest.bdd
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_heatM hφ.diff hφ.cont hφ.dtest.cont hC hC' a x).differentiableAt,
      by simp, ?_⟩
    rw [hφ.deriv_heatM]
    exact ih hφ.dtest

theorem heatM_nonneg {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) (a x : ℝ) : 0 ≤ heatM a φ x :=
  integral_nonneg fun z => hφ _


lemma integrable_prod_comp {φ : ℝ → ℝ} (hc : Continuous φ) (hi : Integrable φ volume) (a : ℝ) :
    Integrable (fun p : ℝ × ℝ => φ (p.1 - a * p.2)) (volume.prod (gaussianReal 0 1)) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => φ (p.1 - a * p.2))
      (volume.prod (gaussianReal 0 1)) := (hc.comp (by fun_prop)).aestronglyMeasurable
  rw [integrable_prod_iff' hm]
  refine ⟨ae_of_all _ fun z => hi.comp_sub_right (a * z), ?_⟩
  have : (fun z : ℝ => ∫ x, ‖φ (x - a * z)‖) = fun _ => ∫ x, ‖φ x‖ := by
    funext z
    exact integral_sub_right_eq_self (fun x => ‖φ x‖) (a * z)
  simp only [this]
  exact integrable_const _

lemma integrable_heatM_gen {φ : ℝ → ℝ} (hc : Continuous φ) (hi : Integrable φ volume) (a : ℝ) :
    Integrable (heatM a φ) volume :=
  (integrable_prod_comp hc hi a).integral_prod_left

lemma integral_heatM_gen {φ : ℝ → ℝ} (hc : Continuous φ) (hi : Integrable φ volume) (a : ℝ) :
    ∫ x, heatM a φ x = ∫ x, φ x := by
  have := integral_integral_swap (μ := volume) (ν := gaussianReal 0 1)
    (f := fun x z => φ (x - a * z)) (integrable_prod_comp hc hi a)
  unfold heatM
  rw [this]
  simp only [integral_sub_right_eq_self φ]
  simp

lemma abs_heatM_le {φ : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (a x : ℝ) :
    |heatM a φ x| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
    (f := fun z => φ (x - a * z)) (C := C) (ae_of_all _ fun z => by simpa using hC _)
  simpa [heatM] using this

lemma memLp_two_heatM_gen {φ : ℝ → ℝ} (hc : Continuous φ) (hi : Integrable φ volume) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) (a : ℝ) : MemLp (heatM a φ) 2 volume := by
  have hint := integrable_heatM_gen hc hi a
  rw [memLp_two_iff_integrable_sq hint.aestronglyMeasurable]
  refine Integrable.mono' (hint.norm.const_mul C) (hint.aestronglyMeasurable.pow 2)
    (ae_of_all _ fun x => ?_)
  have h0 := abs_heatM_le hC a x
  simp only [Real.norm_eq_abs, Pi.pow_apply, abs_pow, sq_abs]
  nlinarith [abs_nonneg (heatM a φ x), sq_abs (heatM a φ x)]

theorem IsTest.integrable {φ : ℝ → ℝ} (hφ : IsTest φ) : Integrable φ volume :=
  hφ.cont.integrable_of_hasCompactSupport hφ.2

theorem IsTest.integrable_heatM {φ : ℝ → ℝ} (hφ : IsTest φ) (a : ℝ) :
    Integrable (heatM a φ) volume :=
  integrable_heatM_gen hφ.cont hφ.integrable a

theorem IsTest.memLp_heatM {φ : ℝ → ℝ} (hφ : IsTest φ) (a : ℝ) :
    MemLp (heatM a φ) 2 volume := by
  obtain ⟨C, -, hC⟩ := hφ.bdd
  exact memLp_two_heatM_gen hφ.cont hφ.integrable hC a

/-- the `L²` class of `heatM b φ`. -/
noncomputable def heatL2 {φ : ℝ → ℝ} (hφ : IsTest φ) (b : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (hφ.memLp_heatM b).toLp (heatM b φ)

theorem IsTest.integral_heatM {φ : ℝ → ℝ} (hφ : IsTest φ) (a : ℝ) :
    ∫ x, heatM a φ x = ∫ x, φ x :=
  integral_heatM_gen hφ.cont hφ.integrable a

lemma gauss_neg_mp : MeasurePreserving (fun z : ℝ => -z) (gaussianReal 0 1) (gaussianReal 0 1) :=
  ⟨measurable_neg, by simpa using gaussianReal_map_neg (μ := 0) (v := 1)⟩

lemma integral_gauss_neg (f : ℝ → ℝ) :
    ∫ z, f (-z) ∂(gaussianReal 0 1) = ∫ z, f z ∂(gaussianReal 0 1) :=
  gauss_neg_mp.integral_comp (MeasurableEquiv.neg ℝ).measurableEmbedding f

theorem IsTest.integral_mul_heatM_comm {φ ψ : ℝ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ) (a : ℝ) :
    ∫ x, ψ x * heatM a φ x = ∫ x, φ x * heatM a ψ x := by
  obtain ⟨C, -, hC⟩ := hφ.bdd
  obtain ⟨D, -, hD⟩ := hψ.bdd
  have h1 : ∀ x, ψ x * heatM a φ x = ∫ z, ψ x * φ (x - a * z) ∂(gaussianReal 0 1) := fun x => by
    unfold heatM; rw [integral_const_mul]
  have h2 : ∀ y, φ y * heatM a ψ y = ∫ z, φ y * ψ (y + a * z) ∂(gaussianReal 0 1) := fun y => by
    unfold heatM
    rw [← integral_const_mul, ← integral_gauss_neg (fun z => φ y * ψ (y - a * z))]
    simp
  simp only [h1, h2]
  have hint1 : Integrable (Function.uncurry fun (x z : ℝ) => ψ x * φ (x - a * z))
      (volume.prod (gaussianReal 0 1)) := by
    refine Integrable.mono' ((hψ.integrable.norm.comp_fst (gaussianReal 0 1)).const_mul C)
      ((hψ.cont.comp continuous_fst).mul (hφ.cont.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs, mul_one]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
  have hint2 : Integrable (Function.uncurry fun (z y : ℝ) => φ y * ψ (y + a * z))
      ((gaussianReal 0 1).prod volume) := by
    refine Integrable.mono' ((hφ.integrable.norm.comp_snd (gaussianReal 0 1)).const_mul D)
      ((hφ.cont.comp continuous_snd).mul (hψ.cont.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
    rw [mul_comm D]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  rw [integral_integral_swap hint1, ← integral_integral_swap hint2]
  congr 1
  funext z
  have := integral_add_right_eq_self (μ := volume) (fun x => ψ x * φ (x - a * z)) (a * z)
  simp only [add_sub_cancel_right] at this
  rw [← this]
  congr 1
  funext y
  ring


lemma qmp_affine {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    Measure.QuasiMeasurePreserving (fun z : ℝ => x - a * z) volume volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun z : ℝ => a * z) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [Real.map_volume_mul_left ha]
    exact Measure.smul_absolutelyContinuous
  exact (volume.measurePreserving_sub_left x).quasiMeasurePreserving.comp h1

lemma ae_gauss_affine {a : ℝ} (ha : a ≠ 0) (x : ℝ) {P : ℝ → Prop}
    (h : ∀ᵐ y ∂(volume : Measure ℝ), P y) : ∀ᵐ z ∂(gaussianReal 0 1), P (x - a * z) :=
  (gaussianReal_absolutelyContinuous 0 one_ne_zero).ae_le ((qmp_affine ha x).ae h)

/-- `heatM a φ → 1` pointwise (every `x`, `a ≠ 0`) if `φₙ → 1` a.e. with `|φₙ| ≤ 1` a.e. -/
theorem heatM_tendsto_one {a : ℝ} (ha : a ≠ 0) {u : ℕ → ℝ → ℝ} (hmeas : ∀ n, Measurable (u n))
    (hle : ∀ n, ∀ᵐ y ∂(volume : Measure ℝ), |u n y| ≤ 1)
    (hlim : ∀ᵐ y ∂(volume : Measure ℝ), Tendsto (fun n => u n y) atTop (𝓝 1)) (x : ℝ) :
    Tendsto (fun n => heatM a (u n) x) atTop (𝓝 1) := by
  have h1 : ∫ z, (1:ℝ) ∂(gaussianReal 0 1) = 1 := by simp
  rw [← h1]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    (fun n => ((hmeas n).comp (by fun_prop)).aestronglyMeasurable) (integrable_const _)
    (fun n => ?_) ?_
  · filter_upwards [ae_gauss_affine ha x (hle n)] with z hz
    simpa using hz
  · filter_upwards [ae_gauss_affine ha x hlim] with z hz using hz


lemma gauss_pdf_hasDerivAt (z : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-z * gaussianPDFReal 0 1 z) z := by
  have h : gaussianPDFReal 0 1 = fun z => (√(2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2) := by
    funext z; simp [gaussianPDFReal]
  rw [h]
  have := (((hasDerivAt_pow 2 z).neg.div_const 2).exp).const_mul (√(2 * Real.pi))⁻¹
  convert this using 1
  simp
  ring

lemma integrable_id_mul_pdf : Integrable (fun z : ℝ => z * gaussianPDFReal 0 1 z) := by
  have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul (√(2 * Real.pi))⁻¹
  convert this using 2 with z
  simp [gaussianPDFReal]
  ring

lemma gauss_ibp {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (hgc : Continuous g)
    (hg'c : Continuous g') {B B' : ℝ} (hB : ∀ x, |g x| ≤ B) (hB' : ∀ x, |g' x| ≤ B') :
    ∫ z, z * g z ∂(gaussianReal 0 1) = ∫ z, g' z ∂(gaussianReal 0 1) := by
  have hpi := integrable_gaussianPDFReal 0 1
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g) (u' := g')
    (v := gaussianPDFReal 0 1) (v' := fun z => -z * gaussianPDFReal 0 1 z)
    (fun x _ => hg x) (fun x _ => gauss_pdf_hasDerivAt x)
    (by
      have := integrable_id_mul_pdf.neg.bdd_mul hgc.aestronglyMeasurable
        (ae_of_all _ fun x => by simpa using hB x)
      convert this using 2 with z
      simp)
    (hpi.bdd_mul hg'c.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hB' x))
    (hpi.bdd_mul hgc.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hB x))
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have e1 : ∫ z, g z * (-z * gaussianPDFReal 0 1 z) = -∫ z, gaussianPDFReal 0 1 z * (z * g z) := by
    rw [← integral_neg]
    congr 1; funext z; ring
  have e2 : ∫ z, g' z * gaussianPDFReal 0 1 z = ∫ z, gaussianPDFReal 0 1 z * g' z := by
    congr 1; funext z; ring
  rw [e1, e2] at h
  linarith


lemma taylor_bound {φ : ℝ → ℝ} (hφ : IsTest φ) {C₂ : ℝ} (hC₂ : ∀ x, |deriv (deriv φ) x| ≤ C₂)
    (y t : ℝ) : |φ (y - t) - φ y + t * deriv φ y| ≤ C₂ * t ^ 2 := by
  have hC0 : 0 ≤ C₂ := (abs_nonneg _).trans (hC₂ 0)
  have hlip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v| := fun u v => by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv φ) (C := C₂) (s := Set.univ)
      (x := v) (y := u) (fun x _ => hφ.dtest.diff x) (fun x _ => by simpa using hC₂ x)
      convex_univ trivial trivial
    simpa using this
  set G : ℝ → ℝ := fun s => φ (y - s) - φ y + s * deriv φ y with hG
  have hGd : ∀ s, HasDerivAt G (-deriv φ (y - s) + deriv φ y) s := fun s => by
    have h1 := ((hφ.diff (y - s)).hasDerivAt).comp_const_sub y s
    have h2 := (h1.sub_const (φ y)).add ((hasDerivAt_id s).mul_const (deriv φ y))
    have h3 : HasDerivAt ((fun x => φ (y - x) - φ y) + fun y_1 => y_1 * deriv φ y)
        (-deriv φ (y - s) + deriv φ y) s := by simpa using h2
    exact h3
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := G) (C := C₂ * |t|)
    (s := Metric.closedBall (0 : ℝ) |t|) (x := 0) (y := t)
    (fun x _ => (hGd x).differentiableAt)
    (fun x hx => by
      rw [(hGd x).deriv, Real.norm_eq_abs]
      have := hlip y (y - x)
      simp only [sub_sub_cancel] at this
      have hx' : |x| ≤ |t| := by simpa using hx
      calc |-deriv φ (y - x) + deriv φ y| = |deriv φ y - deriv φ (y - x)| := by
            rw [neg_add_eq_sub, abs_sub_comm]
        _ ≤ C₂ * |x| := this
        _ ≤ C₂ * |t| := mul_le_mul_of_nonneg_left hx' hC0)
    (convex_closedBall _ _) (by simp) (by simp)
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, Real.norm_eq_abs, Real.norm_eq_abs] at this
  calc _ ≤ C₂ * |t| * |t| := by simpa [hG] using this
    _ = C₂ * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

lemma IsTest.exists_support {φ : ℝ → ℝ} (hφ : IsTest φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < |y| → φ y = 0 ∧ deriv φ y = 0 := by
  obtain ⟨R, hR⟩ := hφ.2.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩
  have hy' : y ∉ tsupport φ := fun hmem => by
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact absurd (lt_of_le_of_lt (le_max_left _ _) hy) (not_lt.2 this)
  exact ⟨image_eq_zero_of_notMem_tsupport hy',
    image_eq_zero_of_notMem_tsupport (fun h => hy' (tsupport_deriv_subset h))⟩

lemma integrable_id_gauss : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal 1).integrable (by simp)

lemma integrable_abs_pow_gauss (n : ℕ) : Integrable (fun z : ℝ => |z| ^ n) (gaussianReal 0 1) := by
  by_cases hn : n = 0
  · subst hn; simpa using integrable_const (1 : ℝ)
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) (n : NNReal)).integrable_norm_pow
    (by simpa using hn)
  simpa using this


/-- the integrand of the remainder of the difference quotient. -/
noncomputable def rho (φ : ℝ → ℝ) (a h x z : ℝ) : ℝ :=
  (φ (x - (a + h) * z) - φ (x - a * z)) / h + z * deriv φ (x - a * z)

lemma rho_bound {φ : ℝ → ℝ} (hφ : IsTest φ) {C₂ : ℝ} (hC₂ : ∀ x, |deriv (deriv φ) x| ≤ C₂)
    (a : ℝ) {h : ℝ} (hh : h ≠ 0) (x z : ℝ) : |rho φ a h x z| ≤ C₂ * |h| * z ^ 2 := by
  have := taylor_bound hφ hC₂ (x - a * z) (h * z)
  have e : rho φ a h x z =
      (φ (x - a * z - h * z) - φ (x - a * z) + h * z * deriv φ (x - a * z)) / h := by
    unfold rho
    have : x - (a + h) * z = x - a * z - h * z := by ring
    rw [this]
    field_simp
  rw [e, abs_div, div_le_iff₀ (abs_pos.2 hh)]
  calc _ ≤ C₂ * (h * z) ^ 2 := this
    _ = C₂ * |h| * z ^ 2 * |h| := by rw [mul_pow, ← sq_abs h]; ring

lemma rho_eq_zero {φ : ℝ → ℝ} (a : ℝ) {R : ℝ} (hR : ∀ y, R < |y| → φ y = 0 ∧ deriv φ y = 0)
    {h : ℝ} (hh : |h| ≤ 1) {x z : ℝ} (hx : R + (|a| + 1) * |z| < |x|) :
    rho φ a h x z = 0 := by
  have h1 : R < |x - (a + h) * z| := by
    have := abs_sub_abs_le_abs_sub x ((a + h) * z)
    have h2 : |(a + h) * z| ≤ (|a| + 1) * |z| := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      calc |a + h| ≤ |a| + |h| := abs_add_le _ _
        _ ≤ |a| + 1 := by linarith
    linarith
  have h3 : R < |x - a * z| := by
    have := abs_sub_abs_le_abs_sub x (a * z)
    have h2 : |a * z| ≤ (|a| + 1) * |z| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    linarith
  unfold rho
  rw [(hR _ h1).1, (hR _ h3).1, (hR _ h3).2]
  simp

lemma integral_abs_rho_le {φ : ℝ → ℝ} (hφ : IsTest φ) {C₂ : ℝ}
    (hC₂ : ∀ x, |deriv (deriv φ) x| ≤ C₂) (a : ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, R < |y| → φ y = 0 ∧ deriv φ y = 0)
    {h : ℝ} (hh0 : h ≠ 0) (hh : |h| ≤ 1) (z : ℝ) :
    ∫ x, |rho φ a h x z| ≤
      |h| * (2 * C₂ * R * |z| ^ 2 + 2 * C₂ * (|a| + 1) * |z| ^ 3) := by
  set L := R + (|a| + 1) * |z| with hL
  have hL0 : 0 ≤ L := by positivity
  have hz0 : ∀ x ∉ Set.Icc (-L) L, |rho φ a h x z| = 0 := fun x hx => by
    rw [rho_eq_zero a hR hh ?_, abs_zero]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (show x < 0 by linarith)]; linarith
    · rw [abs_of_pos (show 0 < x by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz0]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (-L) L)
    (C := C₂ * |h| * z ^ 2) (f := fun x => |rho φ a h x z|) (by simp)
    (fun x _ => by simpa using rho_bound hφ hC₂ a hh0 x z)
  rw [Real.norm_eq_abs, Real.volume_real_Icc, max_eq_left (by linarith)] at this
  refine (le_trans (le_abs_self _) this).trans ?_
  have hz2 : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
  rw [hz2]
  have : L - -L = 2 * R + 2 * (|a| + 1) * |z| := by rw [hL]; ring
  rw [this]
  apply le_of_eq
  ring


lemma rho_integrable {φ : ℝ → ℝ} (hφ : IsTest φ) {C₂ : ℝ} (hC₂ : ∀ x, |deriv (deriv φ) x| ≤ C₂)
    (a : ℝ) {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ y, R < |y| → φ y = 0 ∧ deriv φ y = 0)
    {h : ℝ} (hh0 : h ≠ 0) (hh : |h| ≤ 1) :
    Integrable (fun p : ℝ × ℝ => rho φ a h p.1 p.2) (volume.prod (gaussianReal 0 1)) := by
  have hcont : Continuous (fun p : ℝ × ℝ => rho φ a h p.1 p.2) := by
    have := hφ.cont
    have := hφ.dtest.cont
    unfold rho
    fun_prop
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun z => ?_, ?_⟩
  · have h1 := hφ.integrable.comp_sub_right ((a + h) * z)
    have h2 := hφ.integrable.comp_sub_right (a * z)
    have h3 := hφ.dtest.integrable.comp_sub_right (a * z)
    exact ((h1.sub h2).div_const h).add (h3.const_mul z)
  · refine Integrable.mono'
      (g := fun z => |h| * (2 * C₂ * R * |z| ^ 2 + 2 * C₂ * (|a| + 1) * |z| ^ 3)) ?_ ?_
      (ae_of_all _ fun z => ?_)
    · exact (((integrable_abs_pow_gauss 2).const_mul _).add
        ((integrable_abs_pow_gauss 3).const_mul _)).const_mul _
    · have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖rho φ a h p.1 p.2‖)
          (volume.prod (gaussianReal 0 1)) := hcont.norm.aestronglyMeasurable
      exact hm.prod_swap.integral_prod_right'
    · rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      simpa using integral_abs_rho_le hφ hC₂ a hR0 hR hh0 hh z

lemma integral_rho {φ : ℝ → ℝ} (hφ : IsTest φ) (a : ℝ) {h : ℝ} (hh0 : h ≠ 0) (x : ℝ) :
    ∫ z, rho φ a h x z ∂(gaussianReal 0 1) =
      (heatM (a + h) φ x - heatM a φ x) / h - a * heatM a (deriv (deriv φ)) x := by
  obtain ⟨C, -, hC⟩ := hφ.bdd
  obtain ⟨C', -, hC'⟩ := hφ.dtest.bdd
  obtain ⟨C'', -, hC''⟩ := hφ.dtest.dtest.bdd
  have i1 := integrable_comp_gauss hφ.cont hC (a + h) x
  have i2 := integrable_comp_gauss hφ.cont hC a x
  have i3 : Integrable (fun z => z * deriv φ (x - a * z)) (gaussianReal 0 1) :=
    integrable_id_gauss.mul_bdd (hφ.dtest.cont.comp (by fun_prop)).aestronglyMeasurable
      (c := C') (ae_of_all _ fun z => by simpa using hC' _)
  have hl : ∀ z : ℝ, HasDerivAt (fun z : ℝ => x - a * z) (-a) z := fun z => by
    simpa using ((hasDerivAt_id z).const_mul a).const_sub x
  have ibp := gauss_ibp (g := fun z => deriv φ (x - a * z))
    (g' := fun z => deriv (deriv φ) (x - a * z) * (-a))
    (fun z => by
      have := HasDerivAt.comp z (hφ.dtest.diff (x - a * z)).hasDerivAt (hl z)
      exact this)
    (hφ.dtest.cont.comp (by fun_prop))
    ((hφ.dtest.dtest.cont.comp (by fun_prop)).mul continuous_const) (B := C')
    (B' := C'' * |a|) (fun z => by simpa using hC' _)
    (fun z => by
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (hC'' _) (abs_nonneg _))
  have e1 : Integrable (fun z => (φ (x - (a + h) * z) - φ (x - a * z)) / h) (gaussianReal 0 1) :=
    (i1.sub i2).div_const h
  unfold rho
  rw [integral_add e1 i3, integral_div, integral_sub i1 i2, ibp,
    integral_mul_const]
  unfold heatM
  ring

lemma norm_toLp_le {f : ℝ → ℝ} (hf : MemLp f 2 volume) {S T : ℝ} (hS : 0 ≤ S)
    (hSf : ∀ x, |f x| ≤ S) (hfi : Integrable f volume) (hT : ∫ x, |f x| ≤ T) :
    ‖hf.toLp f‖ ≤ √(S * T) := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have h2 : (2 : ENNReal).toReal = 2 := by simp
  rw [h2, Real.sqrt_eq_rpow, one_div]
  refine Real.rpow_le_rpow (integral_nonneg fun x => by positivity) ?_ (by norm_num)
  have hint : Integrable (fun x => ‖f x‖ ^ (2 : ℝ)) volume := by
    simpa [h2] using hf.integrable_norm_rpow (by norm_num) (by norm_num)
  calc ∫ x, ‖f x‖ ^ (2 : ℝ) ≤ ∫ x, S * |f x| := by
        refine integral_mono hint (hfi.abs.const_mul S) fun x => ?_
        simp only [Real.norm_eq_abs, Real.rpow_two]
        nlinarith [abs_nonneg (f x), hSf x, sq_abs (f x)]
    _ = S * ∫ x, |f x| := integral_const_mul _ _
    _ ≤ S * T := mul_le_mul_of_nonneg_left hT hS


lemma integral_abs_q_le {φ : ℝ → ℝ} (hφ : IsTest φ) {C₂ : ℝ}
    (hC₂ : ∀ x, |deriv (deriv φ) x| ≤ C₂) (a : ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, R < |y| → φ y = 0 ∧ deriv φ y = 0) {h : ℝ} (hh0 : h ≠ 0) (hh : |h| ≤ 1) :
    ∫ x, |∫ z, rho φ a h x z ∂(gaussianReal 0 1)| ≤
      |h| * ((2 * C₂ * R) * ∫ z, |z| ^ 2 ∂(gaussianReal 0 1) +
        (2 * C₂ * (|a| + 1)) * ∫ z, |z| ^ 3 ∂(gaussianReal 0 1)) := by
  have hI := rho_integrable hφ hC₂ a hR0 hR hh0 hh
  have hB : Integrable (fun z : ℝ => |h| * (2 * C₂ * R * |z| ^ 2 + 2 * C₂ * (|a| + 1) * |z| ^ 3))
      (gaussianReal 0 1) :=
    (((integrable_abs_pow_gauss 2).const_mul _).add
      ((integrable_abs_pow_gauss 3).const_mul _)).const_mul _
  calc ∫ x, |∫ z, rho φ a h x z ∂(gaussianReal 0 1)|
      ≤ ∫ x, ∫ z, ‖rho φ a h x z‖ ∂(gaussianReal 0 1) := by
        refine integral_mono hI.integral_prod_left.norm hI.norm.integral_prod_left fun x => ?_
        simpa using norm_integral_le_integral_norm (μ := gaussianReal 0 1)
          (fun z => rho φ a h x z)
    _ = ∫ z, ∫ x, ‖rho φ a h x z‖ ∂volume ∂(gaussianReal 0 1) :=
        integral_integral_swap (f := fun x z => ‖rho φ a h x z‖) hI.norm
    _ ≤ ∫ z, |h| * (2 * C₂ * R * |z| ^ 2 + 2 * C₂ * (|a| + 1) * |z| ^ 3) ∂(gaussianReal 0 1) := by
        refine integral_mono hI.integral_norm_prod_right hB fun z => ?_
        simpa using integral_abs_rho_le hφ hC₂ a hR0 hR hh0 hh z
    _ = _ := by
        rw [integral_const_mul, integral_add ((integrable_abs_pow_gauss 2).const_mul _)
          ((integrable_abs_pow_gauss 3).const_mul _), integral_const_mul, integral_const_mul]

lemma norm_quot_le {φ : ℝ → ℝ} (hφ : IsTest φ) (a : ℝ) {C₂ : ℝ}
    (hC₂ : ∀ x, |deriv (deriv φ) x| ≤ C₂) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, R < |y| → φ y = 0 ∧ deriv φ y = 0) {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) :
    ‖t⁻¹ • (heatL2 hφ (a + t) - heatL2 hφ a) - a • heatL2 hφ.dtest.dtest a‖ ≤
      √((C₂ * ∫ z, z ^ 2 ∂(gaussianReal 0 1)) *
        ((2 * C₂ * R) * ∫ z, |z| ^ 2 ∂(gaussianReal 0 1) +
          (2 * C₂ * (|a| + 1)) * ∫ z, |z| ^ 3 ∂(gaussianReal 0 1))) * |t| := by
  have hC0 : 0 ≤ C₂ := (abs_nonneg _).trans (hC₂ 0)
  set M2 : ℝ := ∫ z, z ^ 2 ∂(gaussianReal 0 1) with hM2
  set T1 : ℝ := (2 * C₂ * R) * ∫ z, |z| ^ 2 ∂(gaussianReal 0 1) +
        (2 * C₂ * (|a| + 1)) * ∫ z, |z| ^ 3 ∂(gaussianReal 0 1) with hT1
  have hz2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) := by
    simpa [sq_abs] using integrable_abs_pow_gauss 2
  set q : ℝ → ℝ := fun x => ∫ z, rho φ a t x z ∂(gaussianReal 0 1) with hq
  have hqe : ∀ x, q x =
      t⁻¹ * (heatM (a + t) φ x - heatM a φ x) - a * heatM a (deriv (deriv φ)) x := by
    intro x
    simp only [hq]
    rw [integral_rho hφ a ht0 x, div_eq_inv_mul]
  have hqi : Integrable q volume := by
    have := (((hφ.integrable_heatM (a + t)).sub (hφ.integrable_heatM a)).const_mul t⁻¹).sub
      ((hφ.dtest.dtest.integrable_heatM a).const_mul a)
    exact this.congr (ae_of_all _ fun x => (hqe x).symm)
  have hqm : MemLp q 2 volume := by
    have := (((hφ.memLp_heatM (a + t)).sub (hφ.memLp_heatM a)).const_mul t⁻¹).sub
      ((hφ.dtest.dtest.memLp_heatM a).const_mul a)
    exact this.ae_eq (ae_of_all _ fun x => (hqe x).symm)
  have hEq : t⁻¹ • (heatL2 hφ (a + t) - heatL2 hφ a) - a • heatL2 hφ.dtest.dtest a
      = hqm.toLp q := by
    unfold heatL2
    rw [← MemLp.toLp_sub, ← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by simp [hqe x])
  rw [hEq]
  have hS : ∀ x, |q x| ≤ (C₂ * M2) * |t| := by
    intro x
    have := norm_integral_le_of_norm_le (μ := gaussianReal 0 1)
      (f := fun z => rho φ a t x z) (g := fun z => C₂ * |t| * z ^ 2) (hz2.const_mul _)
      (ae_of_all _ fun z => by simpa using rho_bound hφ hC₂ a ht0 x z)
    rw [integral_const_mul, Real.norm_eq_abs] at this
    calc |q x| ≤ C₂ * |t| * M2 := this
      _ = _ := by ring
  have hS0 : 0 ≤ (C₂ * M2) * |t| :=
    mul_nonneg (mul_nonneg hC0 (integral_nonneg fun z => sq_nonneg z)) (abs_nonneg _)
  have hT : ∫ x, |q x| ≤ |t| * T1 := integral_abs_q_le hφ hC₂ a hR0 hR ht0 ht1
  have hT1 : 0 ≤ T1 := by
    simp only [hT1]
    have : 0 ≤ ∫ z, |z| ^ 2 ∂(gaussianReal 0 1) := integral_nonneg fun z => by positivity
    have : 0 ≤ ∫ z, |z| ^ 3 ∂(gaussianReal 0 1) := integral_nonneg fun z => by positivity
    positivity
  refine (norm_toLp_le hqm hS0 hS hqi hT).trans (le_of_eq ?_)
  calc √((C₂ * M2 * |t|) * (|t| * T1)) = √((C₂ * M2 * T1) * |t| ^ 2) := by congr 1; ring
    _ = _ := by rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

/-- strong `L²` differentiability in the Gaussian scale `a`: `∂ₐ (heatM a φ) = a · heatM a φ''`. -/
theorem IsTest.hasDerivAt_heatL2 {φ : ℝ → ℝ} (hφ : IsTest φ) (a : ℝ) :
    HasDerivAt (heatL2 hφ) (a • heatL2 hφ.dtest.dtest a) a := by
  obtain ⟨C₂, -, hC₂⟩ := hφ.dtest.dtest.bdd
  obtain ⟨R, hR0, hR⟩ := hφ.exists_support
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      ‖t⁻¹ • (heatL2 hφ (a + t) - heatL2 hφ a) - a • heatL2 hφ.dtest.dtest a‖ ≤ c * |t| :=
    ⟨_, fun t h0 h1 => norm_quot_le hφ a hC₂ hR0 hR h0 h1⟩
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (g := fun t : ℝ => c * |t|) ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) one_pos)] with t ht0 ht1
    have ht1' : |t| ≤ 1 := by simpa using le_of_lt (by simpa using ht1)
    have := hc t (Set.mem_compl_singleton_iff.1 ht0) ht1'
    simpa using this
  · have := (continuous_abs.const_mul c).tendsto (0 : ℝ)
    simpa using this.mono_left nhdsWithin_le_nhds


end MarkovTriple.BGL.Lebesgue
