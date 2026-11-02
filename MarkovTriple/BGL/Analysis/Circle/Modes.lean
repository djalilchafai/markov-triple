import MarkovTriple.BGL.Analysis.Circle.Basic

/-! # The circle: Fourier modes, range of `1 − L`, abstract semigroup lemmas, smoothing

`𝒜 = 𝒜₀ = C^∞(𝕋)`, `L f = f''`, `Γ(f,g) = f' g'`, `μ` = Haar probability measure.
(Ported from the legacy first surface; the legacy `FullMarkovTriple` packaging and
`circle_semigroup_stable` were dropped, see DECISIONS 17.)  The BGL circle instance reuses:

* `circle_esa`: `(1 − L) C^∞(𝕋)` is dense in `L²`.  The real Fourier modes `cos 2πn·`, `sin 2πn·`
  (`mc n`, `ms n`) are eigenfunctions of `L` with eigenvalue `−(2πn)²`; their span `trigSpan`
  contains the trigonometric polynomials (product-to-sum), which are dense; and `1 − L` maps each
  mode onto a multiple of itself.
* `IsSG`/`smoothing`: every strongly continuous contraction-type semigroup `P` whose generator acts on the modes (Banach–Steinhaus),
  strongly continuous, and acts on each mode by `e^{−(2πn)² t}` (right-derivative ODE for the
  orbit + self-adjointness); hence `P_t u` has rapidly decaying Fourier coefficients and is a
  `C^∞` function (a.e.) for every `u ∈ L²` and `t > 0` (`smoothing`).  This also proves
  *uniqueness* of the semigroup on the circle (it is determined on the eigenbasis).
-/


namespace MarkovTriple.Sanity.Circle
section PartModes
open MeasureTheory AddCircle
open scoped ENNReal NNReal Real
/-- real part of `e^{2πinx}` -/
noncomputable def mc (n : ℤ) : 𝕋 → ℝ := fun x => (fourier n x).re
/-- imaginary part of `e^{2πinx}` -/
noncomputable def ms (n : ℤ) : 𝕋 → ℝ := fun x => (fourier n x).im

lemma fourier_pt_add (n : ℤ) (x y : 𝕋) : fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

lemma contDiff_fourier_coe (n : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => fourier n (t : 𝕋)) := by
  have : (fun t : ℝ => fourier n (t : 𝕋)) =
      fun t : ℝ => Complex.exp (2 * π * Complex.I * n / ((1:ℝ):ℂ) * t) := by
    funext t; rw [fourier_coe_apply]; congr 1; ring
  rw [this]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (2 * π * Complex.I * n / ((1:ℝ):ℂ)) * (t : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff (𝕜 := ℝ))
  have hexp : ContDiff ℝ (⊤ : ℕ∞) Complex.exp :=
    Complex.contDiff_exp (𝕜 := ℝ) (n := (⊤ : ℕ∞))
  exact hexp.comp h1

lemma mc_mem (n : ℤ) : mc n ∈ A₀ := by
  rw [mem_A₀]; exact Complex.reCLM.contDiff.comp (contDiff_fourier_coe n)

lemma ms_mem (n : ℤ) : ms n ∈ A₀ := by
  rw [mem_A₀]; exact Complex.imCLM.contDiff.comp (contDiff_fourier_coe n)

lemma hasDerivAt_fourier_shift (n : ℤ) (x : 𝕋) :
    HasDerivAt (fun t : ℝ => fourier n (x + (t : 𝕋)))
      (fourier n x * (2 * π * Complex.I * n)) 0 := by
  have h := hasDerivAt_fourier (1:ℝ) n 0
  simp only [fourier_pt_add]
  have h2 := h.const_mul (fourier n x)
  convert h2 using 1
  simp

lemma D_mc (n : ℤ) : D (mc n) = (-(2 * π * n)) • ms n := by
  funext x
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_fourier_shift n x))
  have : D (mc n) x = _ := h.deriv
  rw [this]
  simp [ms]; ring

lemma D_ms (n : ℤ) : D (ms n) = (2 * π * n) • mc n := by
  funext x
  have h := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_fourier_shift n x))
  have : D (ms n) x = _ := h.deriv
  rw [this]
  simp [mc]; ring

/-- eigenvalue of `-L` on mode `n` -/
noncomputable def lam (n : ℤ) : ℝ := (2 * π * n) ^ 2

lemma lam_nonneg (n : ℤ) : 0 ≤ lam n := sq_nonneg _

lemma Lc_mc (n : ℤ) : Lc (mc n) = (-lam n) • mc n := by
  unfold Lc
  rw [D_mc, D_smul _ (Sm_of_mem (ms_mem n)), D_ms]
  funext x; simp [lam]; ring

lemma Lc_ms (n : ℤ) : Lc (ms n) = (-lam n) • ms n := by
  unfold Lc
  rw [D_ms, D_smul _ (Sm_of_mem (mc_mem n)), D_mc]
  funext x; simp [lam]; ring

/-! ### The span of the modes -/

/-- real trigonometric polynomials: span of all `mc n`, `ms n`. -/
noncomputable def trigSpan : Submodule ℝ (𝕋 → ℝ) := Submodule.span ℝ (Set.range mc ∪ Set.range ms)

lemma V_le_A₀ {f : 𝕋 → ℝ} (hf : f ∈ trigSpan) : f ∈ A₀ := by
  induction hf using Submodule.span_induction with
  | mem x hx => rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> [exact mc_mem n; exact ms_mem n]
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact A₀.smul_mem a hx

lemma fourier_mul_fourier (n m : ℤ) (x : 𝕋) :
    fourier n x * fourier m x = fourier (n + m) x := fourier_add.symm

lemma fourier_mul_conj (n m : ℤ) (x : 𝕋) :
    fourier n x * (starRingEnd ℂ) (fourier m x) = fourier (n + -m) x := by
  rw [fourier_add, fourier_neg]

lemma mc_mul_mc (n m : ℤ) : mc n * mc m = (1/2 : ℝ) • mc (n + m) + (1/2 : ℝ) • mc (n + -m) := by
  funext x
  have h1 := congrArg Complex.re (fourier_mul_fourier n m x)
  have h2 := congrArg Complex.re (fourier_mul_conj n m x)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at h1 h2
  simp only [mc, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [← h1, ← h2]; ring

lemma ms_mul_ms (n m : ℤ) : ms n * ms m = (1/2 : ℝ) • mc (n + -m) + (-1/2 : ℝ) • mc (n + m) := by
  funext x
  have h1 := congrArg Complex.re (fourier_mul_fourier n m x)
  have h2 := congrArg Complex.re (fourier_mul_conj n m x)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at h1 h2
  simp only [ms, mc, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [← h1, ← h2]; ring

lemma mc_mul_ms (n m : ℤ) : mc n * ms m = (1/2 : ℝ) • ms (n + m) + (-1/2 : ℝ) • ms (n + -m) := by
  funext x
  have h1 := congrArg Complex.im (fourier_mul_fourier n m x)
  have h2 := congrArg Complex.im (fourier_mul_conj n m x)
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h1 h2
  simp only [ms, mc, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [← h1, ← h2]; ring

lemma ms_mul_mc (n m : ℤ) : ms n * mc m = (1/2 : ℝ) • ms (n + m) + (1/2 : ℝ) • ms (n + -m) := by
  funext x
  have h1 := congrArg Complex.im (fourier_mul_fourier n m x)
  have h2 := congrArg Complex.im (fourier_mul_conj n m x)
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h1 h2
  simp only [ms, mc, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [← h1, ← h2]; ring

lemma gen_mul_gen {f g : 𝕋 → ℝ} (hf : f ∈ Set.range mc ∪ Set.range ms)
    (hg : g ∈ Set.range mc ∪ Set.range ms) : f * g ∈ trigSpan := by
  have mcV : ∀ n, mc n ∈ trigSpan := fun n => Submodule.subset_span (Or.inl ⟨n, rfl⟩)
  have msV : ∀ n, ms n ∈ trigSpan := fun n => Submodule.subset_span (Or.inr ⟨n, rfl⟩)
  rcases hf with ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> rcases hg with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [mc_mul_mc]; exact add_mem (trigSpan.smul_mem _ (mcV _)) (trigSpan.smul_mem _ (mcV _))
  · rw [mc_mul_ms]; exact add_mem (trigSpan.smul_mem _ (msV _)) (trigSpan.smul_mem _ (msV _))
  · rw [ms_mul_mc]; exact add_mem (trigSpan.smul_mem _ (msV _)) (trigSpan.smul_mem _ (msV _))
  · rw [ms_mul_ms]; exact add_mem (trigSpan.smul_mem _ (mcV _)) (trigSpan.smul_mem _ (mcV _))

lemma V_mul {f g : 𝕋 → ℝ} (hf : f ∈ trigSpan) (hg : g ∈ trigSpan) : f * g ∈ trigSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    induction hg using Submodule.span_induction with
    | mem y hy => exact gen_mul_gen hx hy
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact trigSpan.smul_mem a hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_mul_assoc]; exact trigSpan.smul_mem a hx

lemma const_mem_V (r : ℝ) : (fun _ : 𝕋 => r) ∈ trigSpan := by
  have : (fun _ : 𝕋 => r) = r • mc 0 := by
    funext x; simp [mc]
  rw [this]; exact trigSpan.smul_mem r (Submodule.subset_span (Or.inl ⟨0, rfl⟩))

lemma Atrig_le_V {f : 𝕋 → ℝ} (hf : f ∈ Atrig) : f ∈ trigSpan := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (Or.inl ⟨1, rfl⟩)
    · exact Submodule.subset_span (Or.inr ⟨1, rfl⟩)
  | algebraMap r => exact const_mem_V r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact V_mul hx hy

/-- the range of `1 - L` on `C^∞(𝕋)`, as a submodule -/
noncomputable def rangeR : Submodule ℝ (𝕋 → ℝ) where
  carrier := {f | ∃ g ∈ A₀, f = g - Lc g}
  zero_mem' := ⟨0, zero_mem _, by
    have h0 : D (0 : 𝕋 → ℝ) = 0 := D_const 0
    simp [Lc, h0]⟩
  add_mem' := by
    rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    refine ⟨g + h, add_mem hg hh, ?_⟩
    rw [Lc_add hg hh]; abel
  smul_mem' := by
    rintro c _ ⟨g, hg, rfl⟩
    refine ⟨c • g, A₀.smul_mem c hg, ?_⟩
    rw [Lc_smul c hg, smul_sub]

lemma V_le_R : trigSpan ≤ rangeR := by
  refine Submodule.span_le.2 ?_
  have key : ∀ (f : 𝕋 → ℝ) (n : ℤ), f ∈ A₀ → Lc f = (-lam n) • f → f ∈ (rangeR : Set (𝕋 → ℝ)) := by
    intro f n hf hL
    refine ⟨(1 + lam n)⁻¹ • f, A₀.smul_mem _ hf, ?_⟩
    rw [Lc_smul _ hf, hL]
    have h : (1 + lam n) ≠ 0 := by have := lam_nonneg n; positivity
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rintro f (⟨n, rfl⟩ | ⟨n, rfl⟩)
  · exact key _ n (mc_mem n) (Lc_mc n)
  · exact key _ n (ms_mem n) (Lc_ms n)

/-- trigonometric polynomials are dense in `L²` -/
lemma dense_Atrig :
    Dense {u : Lp ℝ 2 μ₀ | ∃ f ∈ Atrig, (u : 𝕋 → ℝ) =ᵐ[μ₀] f} := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have h1 : DenseRange (ContinuousMap.toLp (E := ℝ) 2 μ₀ ℝ : C(𝕋, ℝ) →L[ℝ] Lp ℝ 2 μ₀) :=
    ContinuousMap.toLp_denseRange ℝ μ₀ ℝ (by simp)
  have h2 : Dense (AC : Set C(𝕋, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, AC_top]; rfl
  have h3 := h1.dense_image (ContinuousMap.toLp (E := ℝ) 2 μ₀ ℝ).continuous h2
  refine h3.mono ?_
  rintro _ ⟨F, hF, rfl⟩
  refine ⟨F, ?_, ContinuousMap.coeFn_toLp _ _⟩
  rw [← AC_map]; exact ⟨F, hF, rfl⟩

/-- **`esa` for the circle**: `(1 - L) C^∞(𝕋)` is dense in `L²`. -/
theorem circle_esa :
    Dense {u : Lp ℝ 2 μ₀ | ∃ f ∈ A₀, (u : 𝕋 → ℝ) =ᵐ[μ₀] f - Lc f} := by
  refine dense_Atrig.mono ?_
  rintro u ⟨f, hf, huf⟩
  obtain ⟨g, hg, rfl⟩ := V_le_R (Atrig_le_V hf)
  exact ⟨g, hg, huf⟩
end PartModes
end MarkovTriple.Sanity.Circle


namespace MarkovTriple.Sanity.Circle
section PartSemigroup
open Filter Topology Set
open scoped NNReal
section Abstract

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- the three semigroup axioms (the only ones used in this section) -/
structure IsSG (P : ℝ≥0 → H →L[ℝ] H) : Prop where
  zero : P 0 = ContinuousLinearMap.id ℝ H
  add : ∀ s t, P (s + t) = (P s).comp (P t)
  cont : ∀ u, Tendsto (fun t => P t u) (𝓝 0) (𝓝 u)

variable {P : ℝ≥0 → H →L[ℝ] H}

lemma IsSG.local_bound (hP : IsSG P) : ∃ δ : ℝ≥0, 0 < δ ∧ ∃ M : ℝ, ∀ t, t ≤ δ → ‖P t‖ ≤ M := by
  by_contra hcon
  push Not at hcon
  have hδ : ∀ n : ℕ, (0 : ℝ≥0) < ((n : ℝ≥0) + 1)⁻¹ := fun n => by positivity
  choose t ht1 ht2 using fun n : ℕ => hcon _ (hδ n) (n : ℝ)
  have htt : Tendsto t atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    refine squeeze_zero (fun n => (t n).2) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have := ht1 n
    have h2 : (t n : ℝ) ≤ (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) := by exact_mod_cast this
    simpa [one_div] using h2
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => P (t n)) (fun x => by
    have := ((hP.cont x).comp htt).norm.bddAbove_range
    obtain ⟨C, hC⟩ := this
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := ht2 n
  have := hC n
  linarith

lemma IsSG.bound_upto (hP : IsSG P) (T : ℝ≥0) : ∃ M : ℝ, ∀ t, t ≤ T → ‖P t‖ ≤ M := by
  obtain ⟨δ, hδ, M0, hM0⟩ := hP.local_bound
  have key : ∀ k : ℕ, ∃ M : ℝ, ∀ t : ℝ≥0, t ≤ k * δ → ‖P t‖ ≤ M := by
    intro k
    induction k with
    | zero =>
      refine ⟨1, fun t ht => ?_⟩
      have : t = 0 := by simpa using ht
      subst this
      rw [hP.zero]; exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      obtain ⟨Mk, hMk⟩ := ih
      refine ⟨M0 * Mk, fun t ht => ?_⟩
      set s := min t δ with hs
      have hst : s ≤ t := min_le_left _ _
      have hsδ : s ≤ δ := min_le_right _ _
      have hr : t - s ≤ k * δ := by
        rcases le_total t δ with h | h
        · have : s = t := min_eq_left h
          rw [this, tsub_self]; exact zero_le
        · have : s = δ := min_eq_right h
          rw [this, tsub_le_iff_right]
          calc t ≤ ((k + 1 : ℕ) : ℝ≥0) * δ := ht
            _ = k * δ + δ := by push_cast; ring
      have : P t = (P s).comp (P (t - s)) := by
        rw [← hP.add]; congr 1; exact (add_tsub_cancel_of_le hst).symm
      rw [this]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul (hM0 s hsδ) (hMk _ hr) (norm_nonneg _) ((norm_nonneg _).trans (hM0 s hsδ))
  obtain ⟨k, hk⟩ := exists_nat_ge (T / δ)
  obtain ⟨M, hM⟩ := key k
  refine ⟨M, fun t ht => hM t (ht.trans ?_)⟩
  rwa [div_le_iff₀ hδ] at hk

lemma IsSG.continuous_apply (hP : IsSG P) (u : H) : Continuous fun t : ℝ≥0 => P t u := by
  rw [continuous_iff_continuousAt]
  intro t0
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := hP.bound_upto t0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t0 le_rfl)
  set w := P t0 u with hw
  obtain ⟨δ1, hδ1, h1⟩ := Metric.tendsto_nhds_nhds.1 (hP.cont w) ε hε
  obtain ⟨δ2, hδ2, h2⟩ := Metric.tendsto_nhds_nhds.1 (hP.cont u) (ε / (M + 1)) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun {t} ht => ?_⟩
  rw [dist_eq_norm]
  rcases le_total t0 t with h | h
  · have e1 : dist (t - t0) 0 = (t : ℝ) - t0 := by
      rw [NNReal.dist_eq, NNReal.coe_sub h]
      simp [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))]
    have e2 : dist t t0 = (t : ℝ) - t0 := by
      rw [NNReal.dist_eq]; exact abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))
    have hd : dist (t - t0) 0 < δ1 := by
      rw [e1, ← e2]; exact lt_of_lt_of_le ht (min_le_left _ _)
    have h4 := h1 hd
    rw [dist_eq_norm] at h4
    have : P t u = P (t - t0) w := by
      rw [hw, ← ContinuousLinearMap.comp_apply, ← hP.add]
      congr 2; rw [tsub_add_cancel_of_le h]
    rw [this]; exact h4
  · have e1 : dist (t0 - t) 0 = (t0 : ℝ) - t := by
      rw [NNReal.dist_eq, NNReal.coe_sub h]
      simp [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))]
    have e2 : dist t t0 = (t0 : ℝ) - t := by
      rw [NNReal.dist_eq, abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))
    have hd : dist (t0 - t) 0 < δ2 := by
      rw [e1, ← e2]; exact lt_of_lt_of_le ht (min_le_right _ _)
    have h4 := h2 hd
    rw [dist_eq_norm] at h4
    have : P t0 u = P t (P (t0 - t) u) := by
      rw [← ContinuousLinearMap.comp_apply, ← hP.add]
      congr 2; rw [add_tsub_cancel_of_le h]
    have e : P t u - P t0 u = - P t (P (t0 - t) u - u) := by
      rw [map_sub, ← this]; abel
    rw [e, norm_neg]
    calc ‖P t (P (t0 - t) u - u)‖ ≤ ‖P t‖ * ‖P (t0 - t) u - u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖P (t0 - t) u - u‖ := mul_le_mul_of_nonneg_right (hM t h) (norm_nonneg _)
      _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left h4.le hM0
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

/-- **eigenvectors of the generator are eigenvectors of the semigroup**. -/
theorem IsSG.eigen (hP : IsSG P) {e : H} {c : ℝ}
    (hgen : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t e - e)) (𝓝[>] 0) (𝓝 ((-c) • e)))
    (t : ℝ≥0) : P t e = Real.exp (-c * t) • e := by
  set y : ℝ → H := fun s => P s.toNNReal e with hy
  have hycont : Continuous y := (hP.continuous_apply e).comp continuous_real_toNNReal
  have hQ : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → P (a + b).toNNReal = (P a.toNNReal).comp (P b.toNNReal) := by
    intro a b ha hb
    rw [Real.toNNReal_add ha hb, hP.add]
  have h1 : Tendsto (fun h : ℝ => h⁻¹ • (y h - e)) (𝓝[>] 0) (𝓝 ((-c) • e)) := by
    have hT : Tendsto Real.toNNReal (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ≥0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := continuous_real_toNNReal.tendsto (0:ℝ)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        exact Real.toNNReal_pos.2 hh
    refine (hgen.comp hT).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp [hy, Real.coe_toNNReal _ (le_of_lt (show (0:ℝ) < h from hh))]
  set φ : ℝ → H := fun s => Real.exp (c * s) • y s with hφ
  have hderiv : ∀ x ∈ Ico (0:ℝ) t, HasDerivWithinAt φ 0 (Ici x) x := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hyd : HasDerivWithinAt y ((-c) • y x) (Ioi x) x := by
      rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
      have h2 : Tendsto (fun s : ℝ => s - x) (𝓝[>] x) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => s - x) (𝓝 x) (𝓝 (x - x)) :=
            (continuous_id.sub continuous_const).tendsto x
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact sub_pos.2 (show x < s from hs)
      have h3 := ((P x.toNNReal).continuous.tendsto _).comp (h1.comp h2)
      rw [map_smul] at h3
      refine h3.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : x < s := hs
      have hsx : 0 ≤ s - x := (sub_pos.2 hs').le
      have e1 : y s = P x.toNNReal (y (s - x)) := by
        have : s = x + (s - x) := by ring
        simp only [hy]
        conv_lhs => rw [this]
        rw [hQ hx0 hsx]; rfl
      simp only [Function.comp, slope_def_module, map_smul, map_sub]
      rw [e1]
    have hexp : HasDerivWithinAt (fun s : ℝ => Real.exp (c * s)) (Real.exp (c * x) * c) (Ioi x) x := by
      have := ((hasDerivAt_id x).const_mul c).exp
      simpa using this.hasDerivWithinAt
    have := hexp.smul hyd
    have h0 : HasDerivWithinAt φ 0 (Ioi x) x := by
      refine this.congr_deriv ?_
      rw [smul_smul, ← add_smul]
      have : Real.exp (c * x) * -c + Real.exp (c * x) * c = 0 := by ring
      rw [this, zero_smul]
    exact h0.Ici_of_Ioi
  have hcont : ContinuousOn φ (Icc 0 (t : ℝ)) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul hycont).continuousOn
  have := constant_of_has_deriv_right_zero hcont hderiv (t : ℝ) ⟨t.2, le_rfl⟩
  have h00 : φ 0 = e := by
    simp [hφ, hy, hP.zero]
  rw [h00] at this
  simp only [hφ, hy, Real.toNNReal_coe] at this
  have e2 : P t e = Real.exp (-c * t) • (Real.exp (c * t) • P t e) := by
    rw [smul_smul, ← Real.exp_add]; simp
  rw [e2, this]

end Abstract
end PartSemigroup
end MarkovTriple.Sanity.Circle


namespace MarkovTriple.Sanity.Circle
section PartSeries
open MeasureTheory AddCircle Filter Topology
open scoped ENNReal NNReal Real
lemma norm_fourier_pt (n : ℤ) (x : 𝕋) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/-- Fourier series with coefficients `c`, as a function of `s ∈ ℝ`. -/
noncomputable def ser (c : ℤ → ℂ) (s : ℝ) : ℂ := ∑' n : ℤ, c n * fourier n (s : 𝕋)

/-- rapid decay -/
def Rapid (c : ℤ → ℂ) : Prop := ∀ k : ℕ, Summable fun n : ℤ => (|(n : ℝ)|) ^ k * ‖c n‖

noncomputable def dcf (c : ℤ → ℂ) : ℤ → ℂ := fun n => (2 * π * Complex.I * n) * c n

lemma Rapid.d {c : ℤ → ℂ} (hc : Rapid c) : Rapid (dcf c) := by
  intro k
  have h := (hc (k + 1)).mul_left (2 * π)
  refine h.congr fun n => ?_
  simp [dcf, abs_of_pos Real.pi_pos]
  ring

lemma Rapid.summable {c : ℤ → ℂ} (hc : Rapid c) : Summable fun n => ‖c n‖ := by
  simpa using hc 0

lemma hasDerivAt_ser {c : ℤ → ℂ} (hc : Rapid c) (s : ℝ) :
    HasDerivAt (ser c) (ser (dcf c) s) s := by
  have hu : Summable fun n : ℤ => ‖dcf c n‖ := by simpa using (hc.d).summable
  have := hasDerivAt_tsum (𝕜 := ℝ) (g := fun (n : ℤ) (y : ℝ) => c n * fourier n (y : 𝕋))
    (g' := fun (n : ℤ) (y : ℝ) => dcf c n * fourier n (y : 𝕋)) (y₀ := 0) hu
    (fun n y => by
      have h := (hasDerivAt_fourier (1:ℝ) n y).const_mul (c n)
      refine h.congr_deriv ?_
      simp only [dcf]; push_cast; ring)
    (fun n y => by rw [norm_mul, norm_fourier_pt, mul_one])
    (by
      refine Summable.of_norm ?_
      simpa [norm_fourier_pt] using hc.summable) s
  exact this

lemma contDiff_ser_nat (k : ℕ) : ∀ c : ℤ → ℂ, Rapid c → ContDiff ℝ k (ser c) := by
  induction k with
  | zero =>
    intro c hc
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_tsum (fun n => continuous_const.mul
      ((fourier n).continuous.comp (AddCircle.continuous_mk' (1:ℝ)))) hc.summable
      (fun n x => by rw [norm_mul, norm_fourier_pt, mul_one])
  | succ k ih =>
    intro c hc
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun s => (hasDerivAt_ser hc s).differentiableAt, by simp, ?_⟩
    have : deriv (ser c) = ser (dcf c) := funext fun s => (hasDerivAt_ser hc s).deriv
    rw [this]
    exact ih _ hc.d

lemma contDiff_ser {c : ℤ → ℂ} (hc : Rapid c) : ContDiff ℝ (⊤ : ℕ∞) (ser c) :=
  contDiff_infty.2 fun k => contDiff_ser_nat k c hc

/-- Gaussian-type weights are rapidly decaying -/
lemma summable_pow_gauss (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℤ => (|(n : ℝ)|) ^ k * Real.exp (-(a * (n : ℝ) ^ 2)) := by
  have hr : Real.exp (-a) < 1 := by simpa using ha
  have hs : Summable fun m : ℕ => ((m : ℝ)) ^ k * Real.exp (-a) ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])
  have h1 : Summable fun m : ℕ => (|((m : ℤ) : ℝ)|) ^ k * Real.exp (-(a * ((m : ℤ) : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
    simp only [Int.cast_natCast, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h
        nlinarith
    nlinarith
  refine Summable.of_nat_of_neg h1 ?_
  refine h1.congr fun m => ?_
  simp

lemma Rapid.of_gauss {a : ℝ} (ha : 0 < a) {c : ℤ → ℂ} {M : ℝ}
    (hM : ∀ n, ‖c n‖ ≤ M * Real.exp (-(a * (n : ℝ) ^ 2))) : Rapid c := by
  intro k
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_pow_gauss k ha).mul_left M)
  calc (|(n : ℝ)|) ^ k * ‖c n‖ ≤ (|(n : ℝ)|) ^ k * (M * Real.exp (-(a * (n : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left (hM n) (by positivity)
    _ = M * ((|(n : ℝ)|) ^ k * Real.exp (-(a * (n : ℝ) ^ 2))) := by ring
end PartSeries
end MarkovTriple.Sanity.Circle


namespace MarkovTriple.Sanity.Circle
section PartFourier
open MeasureTheory AddCircle Filter Topology
open scoped ENNReal NNReal Real InnerProductSpace
noncomputable def mcL (n : ℤ) : Lp ℝ 2 μ₀ := (memLp_of_mem (mc_mem n) 2).toLp (mc n)
noncomputable def msL (n : ℤ) : Lp ℝ 2 μ₀ := (memLp_of_mem (ms_mem n) 2).toLp (ms n)

/-- complexification of an `L²` class -/
noncomputable def liftC (v : Lp ℝ 2 μ₀) : Lp ℂ 2 μ₀ := Complex.ofRealCLM.compLp v

lemma coeFn_liftC (v : Lp ℝ 2 μ₀) :
    (liftC v : 𝕋 → ℂ) =ᵐ[μ₀] fun x => ((v x : ℝ) : ℂ) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp Complex.ofRealCLM v] with x hx
  simpa [liftC] using hx

lemma inner_toLp_left {a : 𝕋 → ℝ} (ha : a ∈ A₀) (v : Lp ℝ 2 μ₀) :
    inner ℝ ((memLp_of_mem ha 2).toLp a) (v) = ∫ x, a x * v x ∂μ₀ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_of_mem ha 2).coeFn_toLp] with x h1
  rw [h1]
  simp [mul_comm]

lemma integrable_mul_Lp {a : 𝕋 → ℝ} (ha : a ∈ A₀) (v : Lp ℝ 2 μ₀) :
    Integrable (fun x => a x * v x) μ₀ := by
  have := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) ((memLp_of_mem ha 2).toLp a) v
  refine (this.congr ?_)
  filter_upwards [(memLp_of_mem ha 2).coeFn_toLp] with x h1
  rw [h1]; simp [mul_comm]

lemma repr_liftC (v : Lp ℝ 2 μ₀) (n : ℤ) :
    (fourierBasis (T := 1)).repr (liftC v) n =
      ((inner ℝ (mcL n) (v) : ℝ) : ℂ) - Complex.I * ((inner ℝ (msL n) (v) : ℝ) : ℂ) := by
  rw [fourierBasis_repr, fourierCoeff]
  have h1 : inner ℝ (mcL n) (v) = ∫ x, mc n x * v x ∂μ₀ := inner_toLp_left (mc_mem n) v
  have h2 : inner ℝ (msL n) (v) = ∫ x, ms n x * v x ∂μ₀ := inner_toLp_left (ms_mem n) v
  rw [h1, h2]
  have e : ∀ x : 𝕋, fourier (-n) x * ((v x : ℝ) : ℂ) =
      ((mc n x * v x : ℝ) : ℂ) - Complex.I * ((ms n x * v x : ℝ) : ℂ) := by
    intro x
    rw [fourier_neg]
    apply Complex.ext <;> simp [mc, ms]
  have i1 := (integrable_mul_Lp (mc_mem n) v).ofReal (𝕜 := ℂ)
  have i2 := ((integrable_mul_Lp (ms_mem n) v).ofReal (𝕜 := ℂ)).const_mul Complex.I
  calc ∫ t, fourier (-n) t • (liftC v) t ∂μ₀
      = ∫ t, (((mc n t * v t : ℝ) : ℂ) - Complex.I * ((ms n t * v t : ℝ) : ℂ)) ∂μ₀ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_liftC v] with x hx
        rw [smul_eq_mul, hx, e]
    _ = _ := by
        refine (integral_sub i1 i2).trans ?_
        rw [integral_const_mul, integral_ofReal, integral_ofReal]
        rfl

lemma norm_repr_le (w : Lp ℂ 2 μ₀) (n : ℤ) : ‖(fourierBasis (T := 1)).repr w n‖ ≤ ‖w‖ := by
  rw [HilbertBasis.repr_apply_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  have : ‖(fourierBasis (T := 1)) n‖ = 1 := (fourierBasis (T := 1)).orthonormal.1 n
  rw [this, one_mul]

section Smoothing

variable {P : ℝ≥0 → Lp ℝ 2 μ₀ →L[ℝ] Lp ℝ 2 μ₀}

lemma eigen_mc (hP : IsSG P)
    (hgen : ∀ f ∈ A₀, ∀ u v : Lp ℝ 2 μ₀, (u : 𝕋 → ℝ) =ᵐ[μ₀] f → (v : 𝕋 → ℝ) =ᵐ[μ₀] Lc f →
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (𝓝[>] 0) (𝓝 v)) (n : ℤ) (t : ℝ≥0) :
    P t (mcL n) = Real.exp (-lam n * t) • mcL n := by
  refine hP.eigen (c := lam n) (hgen (mc n) (mc_mem n) (mcL n) ((-lam n) • mcL n)
    (memLp_of_mem (mc_mem n) 2).coeFn_toLp ?_) t
  filter_upwards [Lp.coeFn_smul (-lam n) (mcL n), (memLp_of_mem (mc_mem n) 2).coeFn_toLp] with x h1 h2
  rw [h1, Pi.smul_apply, show (mcL n : 𝕋 → ℝ) x = mc n x from h2, Lc_mc]; rfl

lemma eigen_ms (hP : IsSG P)
    (hgen : ∀ f ∈ A₀, ∀ u v : Lp ℝ 2 μ₀, (u : 𝕋 → ℝ) =ᵐ[μ₀] f → (v : 𝕋 → ℝ) =ᵐ[μ₀] Lc f →
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (𝓝[>] 0) (𝓝 v)) (n : ℤ) (t : ℝ≥0) :
    P t (msL n) = Real.exp (-lam n * t) • msL n := by
  refine hP.eigen (c := lam n) (hgen (ms n) (ms_mem n) (msL n) ((-lam n) • msL n)
    (memLp_of_mem (ms_mem n) 2).coeFn_toLp ?_) t
  filter_upwards [Lp.coeFn_smul (-lam n) (msL n), (memLp_of_mem (ms_mem n) 2).coeFn_toLp] with x h1 h2
  rw [h1, Pi.smul_apply, show (msL n : 𝕋 → ℝ) x = ms n x from h2, Lc_ms]; rfl

lemma repr_P (hP : IsSG P)
    (hself : ∀ t u v, inner ℝ (P t u) (v) = inner ℝ (u) (P t v))
    (hgen : ∀ f ∈ A₀, ∀ u v : Lp ℝ 2 μ₀, (u : 𝕋 → ℝ) =ᵐ[μ₀] f → (v : 𝕋 → ℝ) =ᵐ[μ₀] Lc f →
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (𝓝[>] 0) (𝓝 v))
    (t : ℝ≥0) (u : Lp ℝ 2 μ₀) (n : ℤ) :
    (fourierBasis (T := 1)).repr (liftC (P t u)) n =
      ((Real.exp (-lam n * t) : ℝ) : ℂ) * (fourierBasis (T := 1)).repr (liftC u) n := by
  rw [repr_liftC, repr_liftC]
  have h1 : inner ℝ (mcL n) (P t u) = Real.exp (-lam n * t) * inner ℝ (mcL n) (u) := by
    rw [← hself, eigen_mc hP hgen, inner_smul_left]; simp
  have h2 : inner ℝ (msL n) (P t u) = Real.exp (-lam n * t) * inner ℝ (msL n) (u) := by
    rw [← hself, eigen_ms hP hgen, inner_smul_left]; simp
  rw [h1, h2]; push_cast; ring

/-- **Smoothing**: for `t > 0`, `P_t u` is (a.e. equal to) a `C^∞` function, for every `u ∈ L²`. -/
theorem smoothing (hP : IsSG P)
    (hself : ∀ t u v, inner ℝ (P t u) (v) = inner ℝ (u) (P t v))
    (hgen : ∀ f ∈ A₀, ∀ u v : Lp ℝ 2 μ₀, (u : 𝕋 → ℝ) =ᵐ[μ₀] f → (v : 𝕋 → ℝ) =ᵐ[μ₀] Lc f →
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (𝓝[>] 0) (𝓝 v))
    {t : ℝ≥0} (ht : 0 < t) (u : Lp ℝ 2 μ₀) :
    ∃ g ∈ A₀, ((P t u : Lp ℝ 2 μ₀) : 𝕋 → ℝ) =ᵐ[μ₀] g := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  set w : Lp ℂ 2 μ₀ := liftC (P t u) with hw
  set b : ℤ → ℂ := fun n => (fourierBasis (T := 1)).repr w n with hb
  have hb' : ∀ n, b n = ((Real.exp (-lam n * t) : ℝ) : ℂ) * (fourierBasis (T := 1)).repr (liftC u) n :=
    fun n => repr_P hP hself hgen t u n
  set a : ℝ := (2 * π) ^ 2 * t with ha
  have hapos : 0 < a := by positivity
  have hbound : ∀ n, ‖b n‖ ≤ ‖liftC u‖ * Real.exp (-(a * (n : ℝ) ^ 2)) := by
    intro n
    rw [hb', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have e : -lam n * t = -(a * (n : ℝ) ^ 2) := by simp only [lam, ha]; ring
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_repr_le _ n) (Real.exp_pos _).le
  have hrap : Rapid b := Rapid.of_gauss hapos hbound
  -- the continuous function `G`
  have hnorm : Summable fun n : ℤ => ‖b n • (fourier n : C(𝕋, ℂ))‖ := by
    refine hrap.summable.congr fun n => ?_
    rw [norm_smul, fourier_norm, mul_one]
  have hsm : Summable (fun n : ℤ => b n • (fourier n : C(𝕋, ℂ))) := Summable.of_norm hnorm
  have hsum : HasSum (fun n : ℤ => b n • (fourier n : C(𝕋, ℂ))) (∑' n : ℤ, b n • (fourier n : C(𝕋, ℂ))) :=
    hsm.hasSum
  obtain ⟨G, hG⟩ : ∃ G : C(𝕋, ℂ), G = ∑' n : ℤ, b n • (fourier n : C(𝕋, ℂ)) := ⟨_, rfl⟩
  rw [← hG] at hsum
  have hL := (ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ).hasSum hsum
  have hL2 : HasSum (fun n : ℤ => b n • (fourierLp (T := 1) 2 n)) w := by
    have := hasSum_fourier_series_L2 w
    simpa only [← fourierBasis_repr] using this
  have hLw : HasSum (fun n : ℤ => b n • (fourierLp (T := 1) 2 n))
      (ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ G) := by
    have e : ∀ n : ℤ, ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ (b n • (fourier n : C(𝕋, ℂ))) =
        b n • (fourierLp (T := 1) 2 n) := fun n => map_smul _ _ _
    have e' : (fun n : ℤ => ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ (b n • (fourier n : C(𝕋, ℂ)))) =
        fun n : ℤ => b n • (fourierLp (T := 1) 2 n) := funext e
    rw [← e']; exact hL
  have hwG : w = ContinuousMap.toLp (E := ℂ) 2 μ₀ ℂ G := hL2.unique hLw
  have hae : (w : 𝕋 → ℂ) =ᵐ[μ₀] G := by
    rw [hwG]; exact ContinuousMap.coeFn_toLp _ _
  have hGs : (fun s : ℝ => G (s : 𝕋)) = ser b := by
    funext s
    have h := ContinuousMap.tsum_apply hsm (s : 𝕋)
    rw [hG]
    refine h.symm.trans ?_
    simp [ser]
  refine ⟨fun x => (G x).re, ?_, ?_⟩
  · rw [mem_A₀]
    have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => G (s : 𝕋)) := by
      rw [hGs]; exact contDiff_ser hrap
    exact Complex.reCLM.contDiff.comp h3
  · filter_upwards [hae, coeFn_liftC (P t u)] with x h1 h2
    rw [hw] at h1
    have : ((P t u : Lp ℝ 2 μ₀) x : ℂ) = G x := by rw [← h2, ← h1]
    rw [← this]; simp

end Smoothing
end PartFourier
end MarkovTriple.Sanity.Circle


namespace MarkovTriple.Sanity.Circle
section PartFull
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
/-- `𝒜 := C^∞(𝕋)`, as a unital subalgebra (same carrier as `A₀`; it contains the constants). -/
def Afull : Subalgebra ℝ (𝕋 → ℝ) where
  carrier := (A₀ : Set (𝕋 → ℝ))
  add_mem' := fun {_ _} hf hg => A₀.add_mem hf hg
  mul_mem' := fun {_ _} hf hg => A₀.mul_mem hf hg
  algebraMap_mem' := fun r => by
    show _ ∈ A₀
    rw [mem_A₀]; exact contDiff_const

lemma mem_Afull {f : 𝕋 → ℝ} : f ∈ Afull ↔ f ∈ A₀ := Iff.rfl

end PartFull
end MarkovTriple.Sanity.Circle
