import Mathlib
import MarkovTriple.BGL.Semigroup.Conservative

/-!
# `P_t 1 = 1` and mass conservation `∫ P_t h = ∫ h`

* For a finite measure (hence a probability measure, D1): S11 for one (equivalently every) exhaustion
  sequence is equivalent to `P_t [1] = [1]` in `L²` (`conservative_iff_semigroup_one`).
  The direction "`P_t 1 = 1` ⇒ S11" uses positivity (monotone a.e. limit), "S11 ⇒ `P_t 1 = 1`" only
  continuity of `P_t` in `L²`.
* Mass conservation `StandardTriple.integral_semigroup`: for a standard triple (S11), for every
  `h ∈ L¹ ∩ L²`, `P_t h ∈ L¹` and `∫ P_t h = ∫ h`.  Proof for `h ≥ 0` by monotone convergence with the
  exhaustion `u_n`: `∫ (P_t h) u_n = ∫ h (P_t u_n)` (self-adjointness) and `0 ≤ P_t u_n ≤ 1`,
  `P_t u_n → 1`; general `h` by splitting into positive and negative parts.
* For finite `μ` and `P_t 1 = 1`: `∫ P_t h = ∫ h` for all `h ∈ L²` (`integral_semigroup_of_one`).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

lemma L2_inner_eq {μ : Measure E} (a b : Lp ℝ 2 μ) :
    inner ℝ a b = ∫ x, a x * b x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_comm])

namespace DiffusionTriple

variable (T : DiffusionTriple E)

/-! ### Finite measure: S11 ⇔ `P_t 1 = 1` -/

section Finite

variable [IsFiniteMeasure T.μ]

/-- The constant `1` as an element of `L²(μ)` (finite measure). -/
noncomputable def one2 : Lp ℝ 2 T.μ := (memLp_const (1 : ℝ)).toLp _

lemma coeFn_one2 : (T.one2 : E → ℝ) =ᵐ[T.μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _

lemma cls_tendsto_one2 {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) :
    Tendsto (fun n => T.cls ⟨u n, hu.1 n⟩) atTop (𝓝 T.one2) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n, ‖T.cls ⟨u n, hu.1 n⟩ - T.one2‖ ^ 2 = ∫ x, (u n x - 1) ^ 2 ∂T.μ := by
    intro n
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (T.cls ⟨u n, hu.1 n⟩) T.one2, coeFn_cls T ⟨u n, hu.1 n⟩,
      T.coeFn_one2] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]; simp [sq]
  have hbd : Integrable (fun x => (|u 0 x| + 1) ^ 2) T.μ :=
    (((memLp2 T (hu.1 0)).norm.add (memLp_const (1 : ℝ)))).integrable_sq.congr
      (Filter.Eventually.of_forall fun x => by simp)
  have hlim : Tendsto (fun n => ∫ x, (u n x - 1) ^ 2 ∂T.μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := T.μ) (fun x => (|u 0 x| + 1) ^ 2)
      (F := fun n x => (u n x - 1) ^ 2) (f := fun _ => (0 : ℝ))
      (fun n => (((memLp2 T (hu.1 n)).aemeasurable.sub aemeasurable_const).pow_const 2).aestronglyMeasurable)
      hbd
      (fun n => by
        filter_upwards [hu.ge_zero_ae, hu.le_one_ae] with x h0 h1
        have a := h0 n
        have b := h1 n
        have c := neg_abs_le (u 0 x)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have : |u n x - 1| ≤ |u 0 x| + 1 := by
          rw [abs_le]; constructor <;> linarith
        calc (u n x - 1) ^ 2 = |u n x - 1| ^ 2 := (sq_abs _).symm
          _ ≤ (|u 0 x| + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2)
      (by
        filter_upwards [hu.2.2] with x hx
        simpa using ((hx.sub_const 1).pow 2))
    simpa using this
  have h2 : Tendsto (fun n => ‖T.cls ⟨u n, hu.1 n⟩ - T.one2‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hlim
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  exact h3.congr (fun n => by simp [Real.sqrt_sq (norm_nonneg _)])

/-- S11 for one exhaustion sequence implies `P_t 1 = 1` in `L²`. -/
theorem semigroup_one_of_conservative {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (t : ℝ≥0)
    (h : ∀ᵐ x ∂T.μ, Tendsto (fun n => (T.exhP hu t n : E → ℝ) x) atTop (𝓝 1)) :
    T.semigroup t T.one2 = T.one2 := by
  have h1 : Tendsto (fun n => T.exhP hu t n) atTop (𝓝 (T.semigroup t T.one2)) :=
    ((T.semigroup t).continuous.tendsto _).comp (T.cls_tendsto_one2 hu)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  refine Lp.ext ?_
  filter_upwards [hae, h, T.coeFn_one2] with x h2 h3 h4
  have h5 := h3.comp hns.tendsto_atTop
  rw [h4]
  exact tendsto_nhds_unique h2 h5

/-- `P_t 1 = 1` in `L²` implies S11 for every exhaustion sequence. -/
theorem conservative_of_semigroup_one {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (t : ℝ≥0)
    (h : T.semigroup t T.one2 = T.one2) :
    ∀ᵐ x ∂T.μ, Tendsto (fun n => (T.exhP hu t n : E → ℝ) x) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => T.exhP hu t n) atTop (𝓝 T.one2) := by
    rw [← h]; exact ((T.semigroup t).continuous.tendsto _).comp (T.cls_tendsto_one2 hu)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  filter_upwards [hae, T.exhP_monotone_ae hu t, T.exhP_le_one_ae hu t, T.coeFn_one2] with x h2 hmono hle h4
  have hbdd : BddAbove (Set.range fun n => (T.exhP hu t n : E → ℝ) x) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact hle n⟩
  have hl := tendsto_atTop_ciSup hmono hbdd
  have h5 := hl.comp hns.tendsto_atTop
  rw [h4] at h2
  have := tendsto_nhds_unique h5 h2
  rwa [this] at hl

/-- For a finite measure: S11 (for the exhaustion sequence `u`) ⇔ `P_t 1 = 1`. -/
theorem conservative_iff_semigroup_one {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (t : ℝ≥0) :
    (∀ᵐ x ∂T.μ, Tendsto (fun n => (T.exhP hu t n : E → ℝ) x) atTop (𝓝 1)) ↔
      T.semigroup t T.one2 = T.one2 :=
  ⟨T.semigroup_one_of_conservative hu t, T.conservative_of_semigroup_one hu t⟩

/-- Finite measure, `P_t 1 = 1`: `∫ P_t h = ∫ h` for every `h ∈ L²`. -/
theorem integral_semigroup_of_one (t : ℝ≥0) (h1 : T.semigroup t T.one2 = T.one2) (h : Lp ℝ 2 T.μ) :
    ∫ x, (T.semigroup t h : E → ℝ) x ∂T.μ = ∫ x, (h : E → ℝ) x ∂T.μ := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    ((formData T).semigroup_isSelfAdjoint t) h T.one2
  have e : inner ℝ (T.semigroup t h) T.one2 = inner ℝ h (T.semigroup t T.one2) := hs
  rw [h1, L2_inner_eq, L2_inner_eq] at e
  have c : ∀ g : Lp ℝ 2 T.μ, ∫ x, g x * T.one2 x ∂T.μ = ∫ x, g x ∂T.μ := fun g =>
    integral_congr_ae (by filter_upwards [T.coeFn_one2] with x hx; rw [hx]; ring)
  rwa [c, c] at e

end Finite

/-! ### Mass conservation -/

section Mass

variable {u : ℕ → E → ℝ}

/-- For `h ≥ 0` in `L¹ ∩ L²` and a nonnegative exhaustion sequence `u` with `P_t u_n → 1` a.e.:
`P_t h ∈ L¹` and `∫ P_t h = ∫ h`. -/
theorem integral_semigroup_nonneg_aux (hu : IsExhaustion T.μ T.A₀ u) (hu0 : ∀ n x, 0 ≤ u n x)
    (t : ℝ≥0) (hcons : ∀ᵐ x ∂T.μ, Tendsto (fun n => (T.exhP hu t n : E → ℝ) x) atTop (𝓝 1))
    (h : Lp ℝ 2 T.μ) (h0 : 0 ≤ᵐ[T.μ] (h : E → ℝ)) (hint : Integrable (h : E → ℝ) T.μ) :
    Integrable (T.semigroup t h : E → ℝ) T.μ ∧
      ∫ x, (T.semigroup t h : E → ℝ) x ∂T.μ = ∫ x, (h : E → ℝ) x ∂T.μ := by
  set Ph : Lp ℝ 2 T.μ := T.semigroup t h with hPh
  have hPh0 : 0 ≤ᵐ[T.μ] (Ph : E → ℝ) := T.semigroup_nonneg t h0
  have hPu0 : ∀ n, 0 ≤ᵐ[T.μ] (T.exhP hu t n : E → ℝ) := fun n =>
    T.semigroup_nonneg t (by
      filter_upwards [coeFn_cls T ⟨u n, hu.1 n⟩] with x hx
      simp only [Pi.zero_apply]; rw [hx]; exact hu0 n x)
  have hPu1 := T.exhP_le_one_ae hu t
  have hsym : ∀ n, ∫ x, (Ph : E → ℝ) x * u n x ∂T.μ =
      ∫ x, (h : E → ℝ) x * (T.exhP hu t n : E → ℝ) x ∂T.μ := by
    intro n
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((formData T).semigroup_isSelfAdjoint t) h (T.cls ⟨u n, hu.1 n⟩)
    have e : inner ℝ Ph (T.cls ⟨u n, hu.1 n⟩) = inner ℝ h (T.exhP hu t n) := hs
    rw [L2_inner_eq, L2_inner_eq] at e
    rw [← integral_congr_ae (by
      filter_upwards [coeFn_cls T ⟨u n, hu.1 n⟩] with x hx
      show (Ph : E → ℝ) x * (T.cls ⟨u n, hu.1 n⟩ : E → ℝ) x = (Ph : E → ℝ) x * u n x
      rw [hx])]
    exact e
  have hInt1 : ∀ n, Integrable (fun x => (Ph : E → ℝ) x * u n x) T.μ := fun n =>
    (Lp.memLp Ph).integrable_mul (memLp2 T (hu.1 n))
  have hInt2 : ∀ n, Integrable (fun x => (h : E → ℝ) x * (T.exhP hu t n : E → ℝ) x) T.μ := by
    intro n
    refine hint.mono' ((Lp.aestronglyMeasurable h).mul (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [h0, hPu0 n, hPu1] with x a b c
    simp only [Pi.zero_apply] at a b
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg a b)]
    exact mul_le_of_le_one_right a (c n)
  have hle : ∀ n, ∫ x, (Ph : E → ℝ) x * u n x ∂T.μ ≤ ∫ x, (h : E → ℝ) x ∂T.μ := by
    intro n
    rw [hsym n]
    refine integral_mono_ae (hInt2 n) hint ?_
    filter_upwards [h0, hPu0 n, hPu1] with x a b c
    simp only [Pi.zero_apply] at a b
    exact mul_le_of_le_one_right a (c n)
  -- integrability of `P_t h` by monotone convergence
  have hmono : ∀ᵐ x ∂T.μ, Monotone fun n => ENNReal.ofReal ((Ph : E → ℝ) x * u n x) := by
    filter_upwards [hPh0, hu.monotone_ae] with x a b n m hnm
    simp only [Pi.zero_apply] at a
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (b hnm) a)
  have htend : ∀ᵐ x ∂T.μ, Tendsto (fun n => ENNReal.ofReal ((Ph : E → ℝ) x * u n x)) atTop
      (𝓝 (ENNReal.ofReal ((Ph : E → ℝ) x))) := by
    filter_upwards [hu.2.2] with x hx
    have := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (Ph : E → ℝ) x)).mul hx)
    simpa using this
  have hlt := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hInt1 n).aemeasurable.ennreal_ofReal) hmono htend
  have hlint : ∀ n, ∫⁻ x, ENNReal.ofReal ((Ph : E → ℝ) x * u n x) ∂T.μ =
      ENNReal.ofReal (∫ x, (Ph : E → ℝ) x * u n x ∂T.μ) := by
    intro n
    refine (ofReal_integral_eq_lintegral_ofReal (hInt1 n) ?_).symm
    filter_upwards [hPh0] with x a
    simp only [Pi.zero_apply] at a ⊢
    exact mul_nonneg a (hu0 n x)
  have hfin : ∫⁻ x, ENNReal.ofReal ((Ph : E → ℝ) x) ∂T.μ ≤ ENNReal.ofReal (∫ x, (h : E → ℝ) x ∂T.μ) :=
    le_of_tendsto' hlt (fun n => by rw [hlint n]; exact ENNReal.ofReal_le_ofReal (hle n))
  have hPhInt : Integrable (Ph : E → ℝ) T.μ :=
    ⟨Lp.aestronglyMeasurable Ph,
      (hasFiniteIntegral_iff_ofReal hPh0).2 (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)⟩
  refine ⟨hPhInt, ?_⟩
  have hA : Tendsto (fun n => ∫ x, (Ph : E → ℝ) x * u n x ∂T.μ) atTop
      (𝓝 (∫ x, (Ph : E → ℝ) x ∂T.μ)) := by
    have := tendsto_integral_of_dominated_convergence (μ := T.μ) (fun x => ‖(Ph : E → ℝ) x‖)
      (F := fun n x => (Ph : E → ℝ) x * u n x) (f := fun x => (Ph : E → ℝ) x)
      (fun n => (hInt1 n).aestronglyMeasurable) hPhInt.norm
      (fun n => by
        filter_upwards [hu.le_one_ae] with x hx
        rw [norm_mul]
        have h1 : ‖u n x‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (hu0 n x)]; exact hx n
        exact mul_le_of_le_one_right (norm_nonneg _) h1)
      (by
        filter_upwards [hu.2.2] with x hx
        simpa using (tendsto_const_nhds (x := (Ph : E → ℝ) x)).mul hx)
    exact this
  have hB : Tendsto (fun n => ∫ x, (h : E → ℝ) x * (T.exhP hu t n : E → ℝ) x ∂T.μ) atTop
      (𝓝 (∫ x, (h : E → ℝ) x ∂T.μ)) := by
    have := tendsto_integral_of_dominated_convergence (μ := T.μ) (fun x => ‖(h : E → ℝ) x‖)
      (F := fun n x => (h : E → ℝ) x * (T.exhP hu t n : E → ℝ) x) (f := fun x => (h : E → ℝ) x)
      (fun n => (hInt2 n).aestronglyMeasurable) hint.norm
      (fun n => by
        filter_upwards [hPu0 n, hPu1] with x a c
        simp only [Pi.zero_apply] at a
        rw [norm_mul]
        have h1 : ‖(T.exhP hu t n : E → ℝ) x‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg a]; exact c n
        exact mul_le_of_le_one_right (norm_nonneg _) h1)
      (by
        filter_upwards [hcons] with x hx
        simpa using (tendsto_const_nhds (x := (h : E → ℝ) x)).mul hx)
    exact this
  have hA' : Tendsto (fun n => ∫ x, (h : E → ℝ) x * (T.exhP hu t n : E → ℝ) x ∂T.μ) atTop
      (𝓝 (∫ x, (Ph : E → ℝ) x ∂T.μ)) := hA.congr hsym
  exact tendsto_nhds_unique hA' hB

end Mass

end DiffusionTriple

namespace StandardTriple

variable (S : StandardTriple E)

lemma abs_max_mul_le (σ a : ℝ) (hσ : |σ| ≤ 1) : |max (σ * a) 0| ≤ |a| := by
  rcases le_total (σ * a) 0 with h | h
  · rw [max_eq_right h]; simpa using abs_nonneg a
  · rw [max_eq_left h, abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hσ

lemma memLp_posPart {μ : Measure E} {f : E → ℝ} (hf : MemLp f 2 μ) (σ : ℝ) (hσ : |σ| ≤ 1) :
    MemLp (fun x => max (σ * f x) 0) 2 μ :=
  hf.of_le ((((aemeasurable_const.mul hf.aemeasurable).max aemeasurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using abs_max_mul_le σ (f x) hσ)

/-- **Mass conservation**: for a standard triple, `h ∈ L¹ ∩ L²` gives `P_t h ∈ L¹` and
`∫ P_t h = ∫ h`. -/
theorem integral_semigroup (t : ℝ≥0) (h : Lp ℝ 2 S.μ) (hint : Integrable (h : E → ℝ) S.μ) :
    Integrable (S.toDiffusionTriple.semigroup t h : E → ℝ) S.μ ∧
      ∫ x, (S.toDiffusionTriple.semigroup t h : E → ℝ) x ∂S.μ = ∫ x, (h : E → ℝ) x ∂S.μ := by
  obtain ⟨u, hu, hu0⟩ := S.toDiffusionTriple.exists_nonneg_exhaustion
  have hcons := S.conservative u hu (fun n => Filter.Eventually.of_forall (hu0 n)) t
  have key := fun (g : Lp ℝ 2 S.μ) (g0 : 0 ≤ᵐ[S.μ] (g : E → ℝ)) (gi : Integrable (g : E → ℝ) S.μ) =>
    S.toDiffusionTriple.integral_semigroup_nonneg_aux hu hu0 t hcons g g0 gi
  -- positive and negative parts
  set hp : Lp ℝ 2 S.μ := (memLp_posPart (Lp.memLp h) 1 (by simp)).toLp _ with hhp
  set hn : Lp ℝ 2 S.μ := (memLp_posPart (Lp.memLp h) (-1) (by simp)).toLp _ with hhn
  have hpc : (hp : E → ℝ) =ᵐ[S.μ] fun x => max (1 * (h : E → ℝ) x) 0 := MemLp.coeFn_toLp _
  have hnc : (hn : E → ℝ) =ᵐ[S.μ] fun x => max (-1 * (h : E → ℝ) x) 0 := MemLp.coeFn_toLp _
  have hp0 : 0 ≤ᵐ[S.μ] (hp : E → ℝ) := by
    filter_upwards [hpc] with x hx; rw [hx]; exact le_max_right _ _
  have hn0 : 0 ≤ᵐ[S.μ] (hn : E → ℝ) := by
    filter_upwards [hnc] with x hx; rw [hx]; exact le_max_right _ _
  have hpi : Integrable (hp : E → ℝ) S.μ := by
    refine hint.norm.mono' (Lp.aestronglyMeasurable hp) ?_
    filter_upwards [hpc] with x hx
    rw [hx]; simp only [Real.norm_eq_abs]
    exact abs_max_mul_le 1 _ (by simp)
  have hni : Integrable (hn : E → ℝ) S.μ := by
    refine hint.norm.mono' (Lp.aestronglyMeasurable hn) ?_
    filter_upwards [hnc] with x hx
    rw [hx]; simp only [Real.norm_eq_abs]
    exact abs_max_mul_le (-1) _ (by simp)
  have hsub : h = hp - hn := by
    refine Lp.ext ?_
    filter_upwards [hpc, hnc, Lp.coeFn_sub hp hn] with x a b c
    rw [c, Pi.sub_apply, a, b]
    rcases le_total ((h : E → ℝ) x) 0 with h1 | h1
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  obtain ⟨k1, k2⟩ := key hp hp0 hpi
  obtain ⟨k3, k4⟩ := key hn hn0 hni
  have e : S.toDiffusionTriple.semigroup t h =
      S.toDiffusionTriple.semigroup t hp - S.toDiffusionTriple.semigroup t hn := by
    rw [hsub]; exact map_sub _ _ _
  have e2 : (S.toDiffusionTriple.semigroup t h : E → ℝ) =ᵐ[S.μ]
      fun x => (S.toDiffusionTriple.semigroup t hp : E → ℝ) x -
        (S.toDiffusionTriple.semigroup t hn : E → ℝ) x := by
    rw [e]; exact Lp.coeFn_sub _ _
  have e3 : (h : E → ℝ) =ᵐ[S.μ] fun x => (hp : E → ℝ) x - (hn : E → ℝ) x := by
    conv_lhs => rw [hsub]
    exact Lp.coeFn_sub _ _
  refine ⟨(k1.sub k3).congr e2.symm, ?_⟩
  rw [integral_congr_ae e2, integral_sub k1 k3, integral_congr_ae e3, integral_sub hpi hni, k2, k4]

end StandardTriple

end MarkovTriple.BGL
