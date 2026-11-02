import Mathlib
import MarkovTriple.BGL.Frozen.PartialDeriv

open MeasureTheory AddCircle
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.Circle

/-- The circle `ℝ/ℤ`. -/
abbrev 𝕋 := AddCircle (1 : ℝ)

/-- derivative along the rotation flow -/
noncomputable def D (f : 𝕋 → ℝ) (x : 𝕋) : ℝ := deriv (fun t : ℝ => f (x + (t : 𝕋))) 0

/-- smooth along rotation lines -/
def Sm (f : 𝕋 → ℝ) : Prop := ∀ x : 𝕋, ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (x + (t : 𝕋)))

noncomputable def cC : C(𝕋, ℝ) := ⟨fun x => (fourier 1 x).re,
  Complex.continuous_re.comp (fourier 1).continuous⟩
noncomputable def sC : C(𝕋, ℝ) := ⟨fun x => (fourier 1 x).im,
  Complex.continuous_im.comp (fourier 1).continuous⟩

lemma cs_shift (x : 𝕋) (t : ℝ) :
    cC (x + (t : 𝕋)) = cC x * Real.cos (2 * π * t) - sC x * Real.sin (2 * π * t) ∧
    sC (x + (t : 𝕋)) = sC x * Real.cos (2 * π * t) + cC x * Real.sin (2 * π * t) := by
  have h : fourier 1 (x + (t : 𝕋)) = fourier 1 x * Complex.exp (2 * π * Complex.I * t) := by
    rw [fourier_apply, fourier_apply, one_smul, one_smul, toCircle_add, Circle.coe_mul]
    have := fourier_coe_apply' (T := 1) (n := 1) (x := t)
    simp only [one_smul, Int.cast_one, mul_one] at this
    rw [this]; simp
  have e : Complex.exp (2 * π * Complex.I * t) =
      (Real.cos (2 * π * t) : ℂ) + (Real.sin (2 * π * t) : ℂ) * Complex.I := by
    have : (2 * π * Complex.I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [e] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre him
  change (fourier 1 (x + (t : 𝕋))).re = _ ∧ (fourier 1 (x + (t : 𝕋))).im = _
  rw [hre, him]
  change _ = (fourier 1 x).re * _ - (fourier 1 x).im * _ ∧ _ = (fourier 1 x).im * _ + (fourier 1 x).re * _
  constructor <;> ring


lemma Sm.hasDerivAt {f : 𝕋 → ℝ} (hf : Sm f) (x : 𝕋) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (x + (u : 𝕋))) (D f (x + (t : 𝕋))) t := by
  have hd : DifferentiableAt ℝ (fun u : ℝ => f (x + (u : 𝕋))) t :=
    ((hf x).differentiable (by simp)).differentiableAt
  have : D f (x + (t : 𝕋)) = deriv (fun u : ℝ => f (x + (u : 𝕋))) t := by
    unfold D
    have : (fun s : ℝ => f (x + (t : 𝕋) + (s : 𝕋))) =
        fun s => (fun u : ℝ => f (x + (u : 𝕋))) (t + s) := by
      funext s; simp [add_assoc]
    rw [this]; simpa using deriv_comp_const_add (fun u : ℝ => f (x + (u : 𝕋))) t 0
  rw [this]; exact hd.hasDerivAt

lemma Sm.hasDerivAt0 {f : 𝕋 → ℝ} (hf : Sm f) (x : 𝕋) :
    HasDerivAt (fun u : ℝ => f (x + (u : 𝕋))) (D f x) 0 := by
  simpa using hf.hasDerivAt x 0

lemma Sm.D {f : 𝕋 → ℝ} (hf : Sm f) : Sm (D f) := by
  intro x
  have : (fun t : ℝ => MarkovTriple.Sanity.Circle.D f (x + (t : 𝕋))) =
      deriv (fun u : ℝ => f (x + (u : 𝕋))) := by
    funext t; exact (hf.hasDerivAt x t).deriv.symm
  rw [this]
  exact (contDiff_infty_iff_deriv.1 (hf x)).2

lemma Sm.add {f g : 𝕋 → ℝ} (hf : Sm f) (hg : Sm g) : Sm (f + g) :=
  fun x => (hf x).add (hg x)

lemma Sm.mul {f g : 𝕋 → ℝ} (hf : Sm f) (hg : Sm g) : Sm (f * g) :=
  fun x => (hf x).mul (hg x)

lemma Sm.const (r : ℝ) : Sm (fun _ => r) := fun _ => contDiff_const

lemma Sm.smul (c : ℝ) {f : 𝕋 → ℝ} (hf : Sm f) : Sm (c • f) :=
  fun x => (contDiff_const.smul (hf x))

lemma D_add {f g : 𝕋 → ℝ} (hf : Sm f) (hg : Sm g) : D (f + g) = D f + D g := by
  funext x
  exact ((hf.hasDerivAt0 x).add (hg.hasDerivAt0 x)).deriv

lemma D_mul {f g : 𝕋 → ℝ} (hf : Sm f) (hg : Sm g) :
    D (f * g) = fun x => D f x * g x + f x * D g x := by
  funext x
  have h : D (f * g) x = _ := ((hf.hasDerivAt0 x).mul (hg.hasDerivAt0 x)).deriv
  simpa using h

lemma D_smul (c : ℝ) {f : 𝕋 → ℝ} (hf : Sm f) : D (c • f) = c • D f := by
  funext x
  have h : D (c • f) x = c * D f x := ((hf.hasDerivAt0 x).const_mul c).deriv
  simpa using h

lemma D_const (r : ℝ) : D (fun _ => r) = 0 := by
  funext x; simp [D]

lemma D_algebraMap (r : ℝ) : D (algebraMap ℝ (𝕋 → ℝ) r) = 0 := D_const r

lemma Sm_c : Sm ⇑cC := by
  intro x
  have : (fun t : ℝ => cC (x + (t : 𝕋))) =
      fun t => cC x * Real.cos (2 * π * t) - sC x * Real.sin (2 * π * t) := by
    funext t; exact (cs_shift x t).1
  rw [this]; fun_prop

lemma Sm_s : Sm ⇑sC := by
  intro x
  have : (fun t : ℝ => sC (x + (t : 𝕋))) =
      fun t => sC x * Real.cos (2 * π * t) + cC x * Real.sin (2 * π * t) := by
    funext t; exact (cs_shift x t).2
  rw [this]; fun_prop

lemma D_c : D ⇑cC = (-(2 * π)) • ⇑sC := by
  funext x
  have h : HasDerivAt (fun t : ℝ => cC x * Real.cos (2 * π * t) - sC x * Real.sin (2 * π * t))
      (-(2 * π) * sC x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_mul (2 * π)
    have := ((h1.cos).const_mul (cC x)).sub ((h1.sin).const_mul (sC x))
    convert this using 1
    simp; ring
  have e : (fun t : ℝ => cC (x + (t : 𝕋))) =
      fun t => cC x * Real.cos (2 * π * t) - sC x * Real.sin (2 * π * t) := by
    funext t; exact (cs_shift x t).1
  unfold D; rw [e, h.deriv]; simp

lemma D_s : D ⇑sC = (2 * π) • ⇑cC := by
  funext x
  have h : HasDerivAt (fun t : ℝ => sC x * Real.cos (2 * π * t) + cC x * Real.sin (2 * π * t))
      (2 * π * cC x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_mul (2 * π)
    have := ((h1.cos).const_mul (sC x)).add ((h1.sin).const_mul (cC x))
    convert this using 1
    simp; ring
  have e : (fun t : ℝ => sC (x + (t : 𝕋))) =
      fun t => sC x * Real.cos (2 * π * t) + cC x * Real.sin (2 * π * t) := by
    funext t; exact (cs_shift x t).2
  unfold D; rw [e, h.deriv]; simp

/-- **the test algebra `𝒜₀ = C^∞(𝕋)`**: smooth functions on the circle, i.e. `f ∘ (↑) : ℝ → ℝ`
is `C^∞`.  It is a *non-unital* subalgebra (it happens to contain the constants), stable under
composition with every smooth `ψ` (in particular those with `ψ(0) = 0`).  The old trigonometric
polynomial algebra is *not* stable under smooth `ψ` and is only used for the density proof
(`Atrig`). -/
def A₀ : NonUnitalSubalgebra ℝ (𝕋 → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t : 𝕋))}
  add_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t : 𝕋)))
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => g (t : 𝕋))) => hf.add hg
  zero_mem' := (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℝ)))
  mul_mem' := fun {f g} (hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t : 𝕋)))
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => g (t : 𝕋))) => hf.mul hg
  smul_mem' := fun c {f} (hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t : 𝕋))) =>
    hf.const_smul c

lemma mem_A₀ {f : 𝕋 → ℝ} : f ∈ A₀ ↔ ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => f (t : 𝕋)) := by
  constructor <;> intro h <;> exact h

lemma Sm_of_contDiff {f : 𝕋 → ℝ} (hf : f ∈ A₀) : Sm f := by
  intro x
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  have : (fun t : ℝ => f ((s : 𝕋) + (t : 𝕋))) = (fun t : ℝ => f (t : 𝕋)) ∘ (fun t => s + t) := by
    funext t; simp [AddCircle.coe_add]
  rw [this]
  exact (mem_A₀.1 hf).comp (contDiff_const.add contDiff_id)

lemma D_coe {f : 𝕋 → ℝ} (hf : f ∈ A₀) (t : ℝ) :
    D f (t : 𝕋) = deriv (fun u : ℝ => f (u : 𝕋)) t := by
  have h := (Sm_of_contDiff hf).hasDerivAt 0 t
  simp only [zero_add] at h
  exact h.deriv.symm

lemma D_mem_A₀ {f : 𝕋 → ℝ} (hf : f ∈ A₀) : D f ∈ A₀ := by
  rw [mem_A₀]
  have : (fun t : ℝ => D f (t : 𝕋)) = deriv (fun u : ℝ => f (u : 𝕋)) := funext (D_coe hf)
  rw [this]
  exact (contDiff_infty_iff_deriv.1 (mem_A₀.1 hf)).2

lemma continuous_of_A₀ {f : 𝕋 → ℝ} (hf : f ∈ A₀) : Continuous f := by
  have hc : Continuous (fun t : ℝ => f (t : 𝕋)) := (mem_A₀.1 hf).continuous
  exact (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hc

lemma A₀_prop {f : 𝕋 → ℝ} (hf : f ∈ A₀) : Sm f ∧ D f ∈ A₀ ∧ Continuous f :=
  ⟨Sm_of_contDiff hf, D_mem_A₀ hf, continuous_of_A₀ hf⟩

/-- the trigonometric polynomials (used only for the density proof) -/
noncomputable def Atrig : Subalgebra ℝ (𝕋 → ℝ) := Algebra.adjoin ℝ {⇑cC, ⇑sC}

lemma cC_coe (t : ℝ) : cC (t : 𝕋) = Real.cos (2 * π * t) := by
  have := (cs_shift 0 t).1
  have c0 : cC 0 = 1 := by simp [cC]
  have s0 : sC 0 = 0 := by simp [sC]
  simpa [c0, s0] using this

lemma sC_coe (t : ℝ) : sC (t : 𝕋) = Real.sin (2 * π * t) := by
  have := (cs_shift 0 t).2
  have c0 : cC 0 = 1 := by simp [cC]
  have s0 : sC 0 = 0 := by simp [sC]
  simpa [c0, s0] using this

lemma Atrig_le {f : 𝕋 → ℝ} (hf : f ∈ Atrig) : f ∈ A₀ := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [mem_A₀]
      simp only [cC_coe]; fun_prop
    · rw [mem_A₀]
      simp only [sC_coe]; fun_prop
  | algebraMap r => rw [mem_A₀]; exact contDiff_const
  | add x y hx hy ihx ihy => exact add_mem ihx ihy
  | mul x y hx hy ihx ihy => exact mul_mem ihx ihy


lemma clm_pi_apply {k : ℕ} (Λ : (Fin k → ℝ) →L[ℝ] ℝ) (v : Fin k → ℝ) :
    Λ v = ∑ i, v i * Λ (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin k → ℝ) = v i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [this, map_smul, smul_eq_mul]

lemma hasDerivAt_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → 𝕋 → ℝ) (hf : ∀ i, Sm (f i)) (x : 𝕋) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ψ (fun i => f i (x + (u : 𝕋))))
      (∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j (x + (t : 𝕋))) * D (f i) (x + (t : 𝕋))) t := by
  have hγ : HasDerivAt (fun u : ℝ => fun i => f i (x + (u : 𝕋)))
      (fun i => D (f i) (x + (t : 𝕋))) t :=
    hasDerivAt_pi.2 fun i => (hf i).hasDerivAt x t
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (fun i => f i (x + (t : 𝕋)))) (fun i => f i (x + (t : 𝕋))) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have := hψd.comp_hasDerivAt t hγ
  refine this.congr_deriv ?_
  rw [clm_pi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold MarkovTriple.BGL.pderiv; ring

lemma D_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → 𝕋 → ℝ) (hf : ∀ i, Sm (f i)) (y : 𝕋) :
    D (fun x => ψ (fun i => f i x)) y =
      ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j y) * D (f i) y := by
  have := (hasDerivAt_comp ψ hψ f hf y 0).deriv
  simpa [D] using this

lemma contDiff_pderiv {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin k) :
    ContDiff ℝ (⊤ : ℕ∞) (MarkovTriple.BGL.pderiv ψ i) := by
  unfold MarkovTriple.BGL.pderiv
  exact (hψ.fderiv_right (by simp)).clm_apply contDiff_const


/-- The Haar probability measure on the circle. -/
noncomputable abbrev μ₀ : Measure 𝕋 := haarAddCircle

lemma bound_of_continuous {f : 𝕋 → ℝ} (hf : Continuous f) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ x)⟩

lemma integral_D {F : 𝕋 → ℝ} (hF : F ∈ A₀) : ∫ x, D F x ∂μ₀ = 0 := by
  obtain ⟨hS, hDmem, hcont⟩ := A₀_prop hF
  have hDc : Continuous (D F) := (A₀_prop hDmem).2.2
  obtain ⟨C, hC⟩ := bound_of_continuous hDc
  have hcm : ∀ t : ℝ, Continuous (fun x : 𝕋 => F (x + (t : 𝕋))) := fun t =>
    hcont.comp (continuous_id.add continuous_const)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ₀)
    (F := fun (t : ℝ) (x : 𝕋) => F (x + (t : 𝕋))) (F' := fun (t : ℝ) (x : 𝕋) => D F (x + (t : 𝕋)))
    (x₀ := 0) (s := Set.univ) (bound := fun _ => C) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcm t).aestronglyMeasurable)
    ((hcm 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hDc.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x t _ => by simpa using hC (x + (t : 𝕋)))
    (integrable_const C)
    (Filter.Eventually.of_forall fun x t _ => by
      have := hS.hasDerivAt x t
      simpa [add_comm] using this)
  have hconst : (fun t : ℝ => ∫ x, F (x + (t : 𝕋)) ∂μ₀) = fun _ => ∫ x, F x ∂μ₀ := by
    funext t; exact integral_add_right_eq_self (μ := μ₀) F (t : 𝕋)
  have h2 := key.2
  rw [hconst] at h2
  have := h2.unique (hasDerivAt_const _ _)
  simpa using this


/-- the same algebra, inside `C(𝕋,ℝ)` -/
noncomputable def AC : Subalgebra ℝ C(𝕋, ℝ) := Algebra.adjoin ℝ {cC, sC}

lemma AC_map : AC.map (ContinuousMap.coeFnAlgHom ℝ) = Atrig := by
  unfold AC Atrig
  rw [AlgHom.map_adjoin, Set.image_insert_eq, Set.image_singleton]
  rfl

lemma AC_mem_A₀ {F : C(𝕋, ℝ)} (hF : F ∈ AC) : (F : 𝕋 → ℝ) ∈ A₀ := by
  have : (F : 𝕋 → ℝ) ∈ Atrig := by rw [← AC_map]; exact ⟨F, hF, rfl⟩
  exact Atrig_le this

lemma AC_sep : AC.SeparatesPoints := by
  intro x y hxy
  have hne : fourier 1 x ≠ fourier 1 y := by
    intro h
    apply hxy
    rw [fourier_apply, fourier_apply, one_smul, one_smul] at h
    exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h)
  by_cases hre : (fourier 1 x).re = (fourier 1 y).re
  · have him : (fourier 1 x).im ≠ (fourier 1 y).im := fun him => hne (Complex.ext hre him)
    exact ⟨sC, ⟨sC, Algebra.subset_adjoin (by simp), rfl⟩, him⟩
  · exact ⟨cC, ⟨cC, Algebra.subset_adjoin (by simp), rfl⟩, hre⟩

lemma AC_top : AC.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints AC AC_sep

lemma dense_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p μ₀ | ∃ f ∈ A₀, (u : 𝕋 → ℝ) =ᵐ[μ₀] f} := by
  have h1 : DenseRange (ContinuousMap.toLp (E := ℝ) p μ₀ ℝ : C(𝕋, ℝ) →L[ℝ] Lp ℝ p μ₀) :=
    ContinuousMap.toLp_denseRange ℝ μ₀ ℝ hp
  have h2 : Dense (AC : Set C(𝕋, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, AC_top]; rfl
  have h3 := h1.dense_image (ContinuousMap.toLp (E := ℝ) p μ₀ ℝ).continuous h2
  refine h3.mono ?_
  rintro _ ⟨F, hF, rfl⟩
  exact ⟨F, AC_mem_A₀ hF, ContinuousMap.coeFn_toLp _ _⟩


/-- generator `L = f''` (second derivative along the rotation flow) -/
noncomputable def Lc (f : 𝕋 → ℝ) : 𝕋 → ℝ := D (D f)

/-- carré du champ `Γ(f,g) = f' g'` -/
noncomputable def Gc (f g : 𝕋 → ℝ) : 𝕋 → ℝ := fun x => D f x * D g x

lemma integrable_of_cont {f : 𝕋 → ℝ} (hf : Continuous f) : Integrable f μ₀ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma memLp_of_mem {f : 𝕋 → ℝ} (hf : f ∈ A₀) (p : ℝ≥0∞) : MemLp f p μ₀ := by
  have hc := (A₀_prop hf).2.2
  obtain ⟨C, hC⟩ := bound_of_continuous hc
  exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

lemma D_mem {f : 𝕋 → ℝ} (hf : f ∈ A₀) : D f ∈ A₀ := (A₀_prop hf).2.1
lemma Sm_of_mem {f : 𝕋 → ℝ} (hf : f ∈ A₀) : Sm f := (A₀_prop hf).1

lemma Gc_mem {f g : 𝕋 → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) : Gc f g ∈ A₀ :=
  mul_mem (D_mem hf) (D_mem hg)

lemma Lc_mem {f : 𝕋 → ℝ} (hf : f ∈ A₀) : Lc f ∈ A₀ := D_mem (D_mem hf)

lemma D_mul' {f g : 𝕋 → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) :
    D (f * g) = D f * g + f * D g := by
  rw [D_mul (Sm_of_mem hf) (Sm_of_mem hg)]; rfl

lemma Lc_mul {f g : 𝕋 → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) (x : 𝕋) :
    Lc (f * g) x = Lc f x * g x + 2 * (D f x * D g x) + f x * Lc g x := by
  unfold Lc
  rw [D_mul' hf hg, D_add (mul_mem (D_mem hf) hg |> Sm_of_mem) (mul_mem hf (D_mem hg) |> Sm_of_mem),
    D_mul' (D_mem hf) hg, D_mul' hf (D_mem hg)]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

lemma ibp_c {f g : 𝕋 → ℝ} (hf : f ∈ A₀) (hg : g ∈ A₀) :
    ∫ x, g x * Lc f x ∂μ₀ = -∫ x, Gc f g x ∂μ₀ := by
  have h0 := integral_D (mul_mem hg (D_mem hf))
  rw [D_mul' hg (D_mem hf)] at h0
  simp only [Pi.add_apply, Pi.mul_apply] at h0
  have i1 : Integrable (fun x => D g x * D f x) μ₀ :=
    integrable_of_cont ((A₀_prop (D_mem hg)).2.2.mul (A₀_prop (D_mem hf)).2.2)
  have i2 : Integrable (fun x => g x * D (D f) x) μ₀ :=
    integrable_of_cont ((A₀_prop hg).2.2.mul (A₀_prop (D_mem (D_mem hf))).2.2)
  rw [integral_add i1 i2] at h0
  have : (fun x => Gc f g x) = fun x => D g x * D f x := by funext x; simp [Gc, mul_comm]
  rw [this]
  unfold Lc
  linarith


lemma diffusion_c (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → 𝕋 → ℝ) (hf : ∀ i, f i ∈ A₀) :
    (∀ g ∈ A₀, Gc (fun x => ψ (fun i => f i x)) g =
        fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * Gc (f i) g x) ∧
      Lc (fun x => ψ (fun i => f i x)) =
        fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * Lc (f i) x +
          ∑ i, ∑ j, MarkovTriple.BGL.pderiv₂ ψ i j (fun l => f l x) * Gc (f i) (f j) x := by
  have hS : ∀ i, Sm (f i) := fun i => Sm_of_mem (hf i)
  have hD : D (fun x => ψ (fun i => f i x)) =
      fun y => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j y) * D (f i) y :=
    funext fun y => D_comp ψ hψ f hS y
  refine ⟨fun g _ => ?_, ?_⟩
  · funext x
    simp only [Gc, hD, Finset.sum_mul, mul_assoc]
  · funext x
    unfold Lc
    rw [hD]
    have e : (x + ((0 : ℝ) : 𝕋)) = x := by simp
    have hi : ∀ i, HasDerivAt (fun u : ℝ => MarkovTriple.BGL.pderiv ψ i
          (fun j => f j (x + (u : 𝕋))) * D (f i) (x + (u : 𝕋)))
        ((∑ j, MarkovTriple.BGL.pderiv (MarkovTriple.BGL.pderiv ψ i) j (fun l => f l x) * D (f j) x)
            * D (f i) x + MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * D (D (f i)) x) 0 := by
      intro i
      have h1 := hasDerivAt_comp (MarkovTriple.BGL.pderiv ψ i) (contDiff_pderiv ψ hψ i) f hS x 0
      have h2 := (hS i).D.hasDerivAt x 0
      have h := h1.mul h2
      rw [e] at h
      exact h
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
    have h3 : D (fun y => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j y) * D (f i) y) x = _ :=
      hsum.deriv
    rw [h3]
    simp only [MarkovTriple.BGL.pderiv₂, Gc, Finset.sum_add_distrib, Finset.sum_mul]
    have : ∀ i j, MarkovTriple.BGL.pderiv (MarkovTriple.BGL.pderiv ψ i) j =
        fun z => fderiv ℝ (fun y => MarkovTriple.BGL.pderiv ψ i y) z (Pi.single j 1) := fun i j => rfl
    simp only [this]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring


lemma Lc_add {g h : 𝕋 → ℝ} (hg : g ∈ A₀) (hh : h ∈ A₀) : Lc (g + h) = Lc g + Lc h := by
  unfold Lc
  rw [D_add (Sm_of_mem hg) (Sm_of_mem hh), D_add (Sm_of_mem (D_mem hg)) (Sm_of_mem (D_mem hh))]

lemma Lc_smul (c : ℝ) {f : 𝕋 → ℝ} (hf : f ∈ A₀) : Lc (c • f) = c • Lc f := by
  unfold Lc
  rw [D_smul c (Sm_of_mem hf), D_smul c (Sm_of_mem (D_mem hf))]

/-- Nontriviality: `Γ(cos 2πx, cos 2πx) ≠ 0` (it is `4π² sin²(2πx)`; at `x = 1/4` it is `4π²`). -/
theorem circle_Γ_ne_zero : Gc ⇑cC ⇑cC ≠ 0 := by
  intro h
  have h1 := congrFun h ((1/4 : ℝ) : 𝕋)
  have h0 := cs_shift 0 (1/4)
  have c0 : cC 0 = 1 := by simp [cC]
  have s0 : sC 0 = 0 := by simp [sC]
  have hs : sC (((1/4 : ℝ)) : 𝕋) = 1 := by
    have := h0.2
    rw [zero_add, c0, s0] at this
    rw [this]
    have : 2 * π * (1/4 : ℝ) = π / 2 := by ring
    rw [this]; simp
  have : Gc ⇑cC ⇑cC (((1/4 : ℝ)) : 𝕋) = (2 * π) ^ 2 := by
    show D ⇑cC _ * D ⇑cC _ = _
    rw [D_c]
    simp only [Pi.smul_apply, smul_eq_mul, hs]
    ring
  rw [this] at h1
  simp at h1

end MarkovTriple.Sanity.Circle
