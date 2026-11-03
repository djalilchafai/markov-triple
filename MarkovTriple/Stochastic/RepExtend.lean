import Mathlib
import MarkovTriple.Stochastic.KernelRep
import MarkovTriple.Stochastic.Bridge

/-!
# Stochastic layer, part 4: extending the kernel representation from a dense test class

Classical statements used: Bakry-Gentil-Ledoux (BGL) Sect. 1.2, inequality (1.2.1) (Jensen:
`P_t φ(f) ≥ φ(P_t f)`) and the remark after Definition 1.2.1 (if `μ` is invariant, `P_t` is a contraction
on the bounded functions of `L^p(μ)`), Sect. 1.2.2 (kernel representation (1.2.4), understood `μ`-a.e.), and
BGL Sect. 3.1.4 / Def. 1.2.2 (the `L²(μ)` semigroup is a contraction, so density extension is legitimate).
Statement: if a family of sub-Markov kernels `κ_t` satisfies `μ.bind κ_t ≤ μ` (sub-invariance), then
`h ↦ κ_t h` is a contraction of `L²(μ)` on bounded measurable `L²` functions
(`lintegral_sq_kernel_le`).  Consequently, if the kernels represent `P_t` on a set `D` of bounded
measurable `L²` functions which is dense in `L²(μ)`, they represent `P_t` on **all** bounded measurable
`L²` functions (`kernelRep_of_dense`): approximate in `L²`, both `P_t` and `κ_t` are `L²`-contractions.
No truncation or monotone-class argument is needed, because the approximants `f ∈ D` are
bounded themselves and `κ_t` is linear on bounded functions.

* `kernelRep_of_dense` : the generic extension;
* `kernelRep_of_testClass`, `KernelBridge.ofTestClass` : the case `D = T.A₀` (axiom D2: bounded,
  measurable, `L²`, dense), from `IsTestClassRep`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- For a real function, `‖f‖₂² = ∫⁻ ofReal (f²)`. -/
lemma eLpNorm_two_sq_eq {μ : Measure E} {f : E → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 2) (by norm_num) hf
  have e1 : (((2 : ℝ≥0)) : ℝ≥0∞) = 2 := by norm_num
  rw [e1] at h
  have e2 : ((2 : ℝ≥0) : ℝ) = (2 : ℝ) := by norm_num
  rw [e2] at h
  have e3 : ∀ x, ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (f x ^ 2) := by
    intro x
    rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
      (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have e4 : eLpNorm f 2 μ ^ (2 : ℝ) = eLpNorm f 2 μ ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [← e4, h]
  exact lintegral_congr e3

/-- Cauchy-Schwarz for a sub-probability measure: `(∫ h dm)² ≤ ∫ h² dm`, `h` bounded measurable. -/
lemma sq_integral_le {m : Measure E} [IsFiniteMeasure m] (hm : m Set.univ ≤ 1) {h : E → ℝ}
    (hh : Measurable h) (hb : ∃ C, ∀ x, |h x| ≤ C) :
    (∫ y, h y ∂m) ^ 2 ≤ ∫ y, h y ^ 2 ∂m := by
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable h m := Integrable.of_bound hh.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hi2 : Integrable (fun y => h y ^ 2) m := Integrable.of_bound (by fun_prop) (C ^ 2)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2)
  set I := ∫ y, h y ∂m with hI
  set Q := ∫ y, h y ^ 2 ∂m with hQ
  have hM : m.real Set.univ ≤ 1 := by
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top hm
  have hM0 : 0 ≤ m.real Set.univ := measureReal_nonneg
  have key : ∫ y, (h y - I) ^ 2 ∂m = Q - 2 * I * I + I ^ 2 * m.real Set.univ := by
    have : ∀ y, (h y - I) ^ 2 = h y ^ 2 - (2 * I) * h y + I ^ 2 := fun y => by ring
    simp_rw [this]
    rw [integral_add (f := fun y => h y ^ 2 - (2 * I) * h y) (g := fun _ => I ^ 2)
      (hi2.sub (hi.const_mul (2 * I))) (integrable_const _),
      integral_sub hi2 (hi.const_mul (2 * I)), integral_const_mul, integral_const]
    simp [hQ, hI, smul_eq_mul]
    ring
  have hnn : 0 ≤ ∫ y, (h y - I) ^ 2 ∂m := integral_nonneg fun y => sq_nonneg _
  rw [key] at hnn
  nlinarith [sq_nonneg I, mul_nonneg (sq_nonneg I) (sub_nonneg.2 hM)]

variable {μ : Measure E}

/-- **`L²(μ)`-contractivity of a sub-invariant sub-Markov kernel** on bounded measurable functions:
`∫⁻ (κ h)² dμ ≤ ∫⁻ h² dμ`.  (Jensen/Cauchy-Schwarz pointwise, then `lintegral_bind` and `μ.bind κ ≤ μ`.) -/
theorem lintegral_sq_kernel_le (κ : Kernel E E) (hsub : ∀ x, κ x Set.univ ≤ 1)
    (hinv : μ.bind κ ≤ μ) {h : E → ℝ} (hh : Measurable h) (hb : ∃ C, ∀ x, |h x| ≤ C) :
    ∫⁻ x, ENNReal.ofReal ((∫ y, h y ∂(κ x)) ^ 2) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ := by
  obtain ⟨C, hC⟩ := hb
  have : IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, fun x => hsub x⟩⟩
  have step1 : ∀ x, ENNReal.ofReal ((∫ y, h y ∂(κ x)) ^ 2) ≤ ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂(κ x) := by
    intro x
    have : IsFiniteMeasure (κ x) := ⟨lt_of_le_of_lt (hsub x) ENNReal.one_lt_top⟩
    have hi2 : Integrable (fun y => h y ^ 2) (κ x) := Integrable.of_bound (by fun_prop) (C ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2)
    rw [← ofReal_integral_eq_lintegral_ofReal hi2 (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (sq_integral_le (hsub x) hh ⟨C, hC⟩)
  have hmeas : Measurable fun y => ENNReal.ofReal (h y ^ 2) := by fun_prop
  calc ∫⁻ x, ENNReal.ofReal ((∫ y, h y ∂(κ x)) ^ 2) ∂μ
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂(κ x) ∂μ := lintegral_mono step1
    _ = ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂(μ.bind κ) :=
        (Measure.lintegral_bind (Kernel.aemeasurable κ) hmeas.aemeasurable).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (h y ^ 2) ∂μ := lintegral_mono' hinv le_rfl

/-- The function `x ↦ ∫ h dκ(x,·)` is measurable and bounded by `|C|` when `|h| ≤ C`. -/
lemma kernel_integral_measurable (κ : Kernel E E) {h : E → ℝ} (hh : Measurable h) :
    Measurable fun x => ∫ y, h y ∂(κ x) :=
  (hh.stronglyMeasurable.integral_kernel (κ := κ)).measurable

/-- `κ h ∈ L²(μ)` for `h` bounded measurable in `L²(μ)`. -/
lemma memLp_kernel_integral (κ : Kernel E E) (hsub : ∀ x, κ x Set.univ ≤ 1)
    (hinv : μ.bind κ ≤ μ) {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (hL : MemLp h 2 μ) : MemLp (fun x => ∫ y, h y ∂(κ x)) 2 μ := by
  have hm := kernel_integral_measurable κ hh
  show eLpNorm _ 2 μ < ∞
  have h1 := lintegral_sq_kernel_le κ hsub hinv hh ⟨C, hC⟩
  have h2 : eLpNorm h 2 μ ^ 2 < ∞ := ENNReal.pow_lt_top hL
  rw [eLpNorm_two_sq_eq hh.aestronglyMeasurable] at h2
  have h3 : eLpNorm (fun x => ∫ y, h y ∂(κ x)) 2 μ ^ 2 < ∞ := by
    rw [eLpNorm_two_sq_eq hm.aestronglyMeasurable]
    exact lt_of_le_of_lt h1 h2
  refine lt_top_iff_ne_top.2 fun hcon => ?_
  rw [hcon] at h3
  simp at h3

/-- The `L²` norm of `κ h` is at most that of `h`. -/
lemma eLpNorm_kernel_le (κ : Kernel E E) (hsub : ∀ x, κ x Set.univ ≤ 1)
    (hinv : μ.bind κ ≤ μ) {h : E → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    eLpNorm (fun x => ∫ y, h y ∂(κ x)) 2 μ ≤ eLpNorm h 2 μ := by
  have hm := kernel_integral_measurable κ hh
  have h1 := lintegral_sq_kernel_le κ hsub hinv hh ⟨C, hC⟩
  rw [← eLpNorm_two_sq_eq hm.aestronglyMeasurable, ← eLpNorm_two_sq_eq hh.aestronglyMeasurable]
    at h1
  exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 h1

/-- **Extension of the representation from a dense test class** (classical: `L²`-contractivity of
`P_t` and, by Jensen + sub-invariance, of `h ↦ κ_t h`; density of `D`).
If sub-Markov kernels `κ_t` with `μ.bind κ_t ≤ μ` represent `P_t` on a set `D` of bounded measurable
`L²` functions dense in `L²(μ)`, then they represent `P_t` on every bounded measurable `L²` function. -/
theorem kernelRep_of_dense {T : DiffusionTriple E} (κ : ℝ≥0 → Kernel E E)
    (hsub : ∀ t x, κ t x Set.univ ≤ 1)
    (hinv : ∀ t, T.μ.bind (κ t) ≤ T.μ)
    (D : Set (E → ℝ))
    (hDmeas : ∀ f ∈ D, Measurable f) (hDbdd : ∀ f ∈ D, ∃ C, ∀ x, |f x| ≤ C)
    (hDL : ∀ f ∈ D, MemLp f 2 T.μ)
    (hDdense : Dense {u : Lp ℝ 2 T.μ | ∃ f ∈ D, (u : E → ℝ) =ᵐ[T.μ] f})
    (hD : ∀ t, ∀ f (hf : f ∈ D),
      (T.semigroup t ((hDL f hf).toLp f) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ t x)) :
    ∀ (t : ℝ≥0) (g : E → ℝ), Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ hL : MemLp g 2 T.μ,
      (T.semigroup t (hL.toLp g) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(κ t x) := by
  intro t g hg ⟨C, hC⟩ hL
  have : IsFiniteKernel (κ t) := ⟨⟨1, ENNReal.one_lt_top, fun x => hsub t x⟩⟩
  have hKg : MemLp (fun x => ∫ y, g y ∂(κ t x)) 2 T.μ :=
    memLp_kernel_integral (κ t) (hsub t) (hinv t) hg hC hL
  -- it suffices to show the two `L²` classes are equal
  suffices hEq : T.semigroup t (hL.toLp g) = hKg.toLp _ by
    have := Lp.ext_iff.1 hEq
    filter_upwards [this, hKg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rw [← sub_eq_zero]
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  -- approximate `g` by `f ∈ D`
  obtain ⟨u, hdist, ⟨f, hfD, hu⟩⟩ :=
    Metric.dense_iff.1 hDdense (hL.toLp g) (ε / 3) (by positivity)
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hdist
  have hfL := hDL f hfD
  have huf : u = hfL.toLp f := Lp.ext (hu.trans hfL.coeFn_toLp.symm)
  obtain ⟨Cf, hCf⟩ := hDbdd f hfD
  have hKf : MemLp (fun x => ∫ y, f y ∂(κ t x)) 2 T.μ :=
    memLp_kernel_integral (κ t) (hsub t) (hinv t) (hDmeas f hfD) hCf hfL
  -- `P_t u = κ f`
  have e1 : T.semigroup t u = hKf.toLp _ := by
    rw [huf]
    refine Lp.ext ?_
    filter_upwards [hD t f hfD, hKf.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  -- `h = g - f`
  have hh : Measurable (g - f) := hg.sub (hDmeas f hfD)
  have hCh : ∀ x, |(g - f) x| ≤ C + Cf := fun x => by
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hC x) (hCf x))
  have hhL : MemLp (g - f) 2 T.μ := hL.sub hfL
  have hKh : MemLp (fun x => ∫ y, (g - f) y ∂(κ t x)) 2 T.μ :=
    memLp_kernel_integral (κ t) (hsub t) (hinv t) hh hCh hhL
  have hKint : ∀ x, ∫ y, (g - f) y ∂(κ t x) =
      (∫ y, g y ∂(κ t x)) - ∫ y, f y ∂(κ t x) := by
    intro x
    have hi : ∀ {k : E → ℝ} {c : ℝ}, Measurable k → (∀ y, |k y| ≤ c) → Integrable k (κ t x) :=
      fun {k c} hk hkc => Integrable.of_bound hk.aestronglyMeasurable c
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hkc y)
    exact integral_sub (hi hg hC) (hi (hDmeas f hfD) hCf)
  -- bound the three terms
  have hsplit : T.semigroup t (hL.toLp g) - hKg.toLp _ =
      T.semigroup t (hL.toLp g - u) + (hKf.toLp _ - hKg.toLp _) := by
    rw [map_sub, e1]; abel
  have hn1 : ‖T.semigroup t (hL.toLp g - u)‖ ≤ ‖hL.toLp g - u‖ :=
    DiffusionTriple.norm_semigroup_apply_le T t _
  have hn2 : ‖hKf.toLp _ - hKg.toLp _‖ ≤ ‖hL.toLp g - u‖ := by
    have e2 : hKf.toLp _ - hKg.toLp _ = -(hKh.toLp _) := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (hKf.toLp _) (hKg.toLp _), hKf.coeFn_toLp, hKg.coeFn_toLp,
        Lp.coeFn_neg (hKh.toLp _), hKh.coeFn_toLp] with x h1 h2 h3 h4 h5
      rw [h1, Pi.sub_apply, h2, h3, h4, Pi.neg_apply, h5, hKint x]; ring
    rw [e2, norm_neg, Lp.norm_toLp]
    have e3 : ‖hL.toLp g - u‖ = (eLpNorm (g - f) 2 T.μ).toReal := by
      rw [huf, ← Lp.norm_toLp (g - f) hhL]
      congr 1
    rw [e3]
    exact ENNReal.toReal_mono hhL.ne (eLpNorm_kernel_le (κ t) (hsub t) (hinv t) hh hCh)
  rw [hsplit]
  calc ‖T.semigroup t (hL.toLp g - u) + (hKf.toLp _ - hKg.toLp _)‖
      ≤ ‖T.semigroup t (hL.toLp g - u)‖ + ‖hKf.toLp _ - hKg.toLp _‖ := norm_add_le _ _
    _ ≤ ‖hL.toLp g - u‖ + ‖hL.toLp g - u‖ := add_le_add hn1 hn2
    _ ≤ ε / 3 + ε / 3 := by gcongr
    _ ≤ ε := by linarith

/-- The representation on `D = T.A₀` (axiom D2: bounded, measurable, `L²`, dense) extends to all
bounded measurable `L²` functions. -/
theorem kernelRep_of_testClass {T : DiffusionTriple E} {κ : ℝ≥0 → Kernel E E}
    (hsub : ∀ t x, κ t x Set.univ ≤ 1) (hinv : ∀ t, T.μ.bind (κ t) ≤ T.μ)
    (h : IsTestClassRep T κ) :
    ∀ (t : ℝ≥0) (g : E → ℝ), Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ hL : MemLp g 2 T.μ,
      (T.semigroup t (hL.toLp g) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(κ t x) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  refine kernelRep_of_dense (D := (T.A₀ : Set (E → ℝ))) κ hsub hinv
    (fun f hf => T.measurable f hf) (fun f hf => T.bounded f hf)
    (fun f hf => T.memLp f hf 2 (by norm_num) (by norm_num))
    (T.dense 2 this (by norm_num)) ?_
  intro t f hf
  exact h t f hf _ (MemLp.coeFn_toLp _)

/-- A kernel semigroup with `μ` invariant that represents `P_t` on the test algebra `𝒜₀` is a
`KernelBridge` (full representation on bounded measurable `L²` functions). -/
noncomputable def KernelBridge.ofTestClass {T : DiffusionTriple E} (S : SubMarkovKernelSemigroup E)
    (hinv : S.IsInvariant T.μ) (h : IsTestClassRep T S.κ) : KernelBridge T where
  toSubMarkovKernelSemigroup := S
  rep := kernelRep_of_testClass S.subMarkov (fun t => (hinv t).le) h
  invariant := hinv

/-- **Well-definedness on `μ`-null modifications** (audit item): the kernels of a `KernelRepresentation`
charge no `μ`-null measurable set, for `μ`-a.e. starting point.  (Apply `rep` to `g = 1_N ≡ 0` in `L²`.)
Hence `∫ g dκ_t(x,·)` does not depend on the chosen representative of `g`, for a.e. `x`. -/
theorem KernelRepresentation.kernel_null_ae {T : DiffusionTriple E} (K : KernelRepresentation T)
    (t : ℝ≥0) {N : Set E} (hN : MeasurableSet N) (h0 : T.μ N = 0) :
    ∀ᵐ x ∂T.μ, K.κ t x N = 0 := by
  set g : E → ℝ := N.indicator (fun _ => (1 : ℝ)) with hg
  have hgm : Measurable g := measurable_const.indicator hN
  have hg0 : g =ᵐ[T.μ] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
    simp [hg, hx]
  have hL : MemLp g 2 T.μ := MemLp.ae_eq hg0.symm MemLp.zero
  have hcls : hL.toLp g = 0 := Lp.ext (hL.coeFn_toLp.trans (hg0.trans (Lp.coeFn_zero ℝ 2 T.μ).symm))
  have hr := K.rep t g hgm ⟨1, fun x => by by_cases h : x ∈ N <;> simp [hg, h]⟩ hL
  rw [hcls, map_zero] at hr
  filter_upwards [hr, Lp.coeFn_zero ℝ 2 T.μ] with x h1 h2
  have hfin : IsFiniteMeasure (K.κ t x) := ⟨lt_of_le_of_lt (K.subMarkov t x) ENNReal.one_lt_top⟩
  have h3 : ∫ y, g y ∂(K.κ t x) = (K.κ t x).real N := by
    simp only [hg]; rw [integral_indicator hN]; simp
  have h4 : (K.κ t x).real N = 0 := by
    rw [← h3, ← h1, h2]; rfl
  rcases (ENNReal.toReal_eq_zero_iff _).1 h4 with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- **A.e. uniqueness of the kernel representation** (finite `μ`, countably generated σ-algebra): two
`KernelRepresentation`s of the same triple have `μ`-a.e. equal kernels, for each `t`.  So the kernels
produced in this round are canonical up to `μ`-null sets of starting points. -/
theorem KernelRepresentation.ae_unique {T : DiffusionTriple E} [IsFiniteMeasure T.μ] [MeasurableSpace.CountablyGenerated E]
    (K K' : KernelRepresentation T) (t : ℝ≥0) : ∀ᵐ x ∂T.μ, K.κ t x = K'.κ t x := by
  have key : ∀ A : Set E, MeasurableSet A → ∀ᵐ x ∂T.μ, K.κ t x A = K'.κ t x A := by
    intro A hA
    have hgm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
    have hb : ∃ C, ∀ x, |A.indicator (fun _ => (1 : ℝ)) x| ≤ C :=
      ⟨1, fun x => by by_cases h : x ∈ A <;> simp [h]⟩
    have hL : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 T.μ := MemLp.of_bound hgm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by by_cases h : x ∈ A <;> simp [h])
    filter_upwards [K.rep t _ hgm hb hL, K'.rep t _ hgm hb hL] with x h1 h2
    have e : ∀ L : KernelRepresentation T, ∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂(L.κ t x)
        = (L.κ t x).real A := fun L => by
      rw [integral_indicator hA]; simp
    rw [e] at h1 h2
    have := h1.symm.trans h2
    simp only [Measure.real] at this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  set S := MeasurableSpace.countableGeneratingSet E with hS
  have hSc : S.Countable := MeasurableSpace.countable_countableGeneratingSet
  have hSm : ∀ A ∈ S, MeasurableSet A := fun A hA =>
    MeasurableSpace.measurableSet_countableGeneratingSet hA
  have hall : ∀ᵐ x ∂T.μ, ∀ A ∈ generatePiSystem S, K.κ t x A = K'.κ t x A := by
    rw [ae_ball_iff (KernelRepresentation.countable_generatePiSystem hSc)]
    exact fun A hA => key A (generatePiSystem_measurableSet hSm A hA)
  filter_upwards [hall, key Set.univ MeasurableSet.univ] with x hx hu
  have : IsFiniteMeasure (K.κ t x) := ⟨lt_of_le_of_lt (K.subMarkov t x) ENNReal.one_lt_top⟩
  exact ext_of_generate_finite (generatePiSystem S)
    (by rw [generateFrom_generatePiSystem_eq]
        exact (MeasurableSpace.generateFrom_countableGeneratingSet (α := E)).symm)
    (isPiSystem_generatePiSystem S) hx hu

end MarkovTriple.Stochastic
