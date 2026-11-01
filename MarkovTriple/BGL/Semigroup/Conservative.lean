import Mathlib
import MarkovTriple.BGL.Semigroup.Markov
import MarkovTriple.BGL.Frozen.StandardTriple

/-!
# Conservativeness (S11): independence of the exhaustion sequence, `P_t 1 = 1`

Everything here is a theorem about the Friedrichs semigroup of a bare `DiffusionTriple`; it uses
only positivity and the sub-Markov property (`BGL/Semigroup/Markov.lean`).

For an exhaustion sequence `u` (`IsExhaustion`, a.e. increasing, a.e. `→ 1`, terms in `𝒜₀`; signs
arbitrary) write `P_t u_n` for `T.semigroup t (T.cls u_n)`.

* `exhP_monotone_ae`, `exhP_le_one_ae`: a.e., `n ↦ P_t u_n` is increasing and `≤ 1`
  (positivity + sub-Markov), hence converges a.e. to a function `ℓ_u ≤ 1`.
* `comparison`: if `v` is another exhaustion sequence then `P_t v_m ≤ ℓ_u` a.e. for all `m`
  (`(v_m − u_n)⁺ → 0` in `L²` by dominated convergence, `P_t` is an `L²` contraction and positive).
* `conservative_transfer`: if `P_t v_n → 1` a.e. for one exhaustion sequence `v` then also for every
  exhaustion sequence `u` (**independence of the exhaustion sequence**; `StandardTriple.conservative_all`
  says that S11 for nonnegative sequences gives S11 for all).
* `exists_nonneg_exhaustion`: nonnegative exhaustion sequences exist (compose with a smooth monotone
  `ψ` with `ψ(t) = 0` for `t ≤ 0`, `ψ(1) = 1`).
* for finite `μ`: S11 ⇔ `P_t 1 = 1` in `L²` (`conservative_iff_semigroup_one`).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-! ### Elementary facts on exhaustion sequences -/

section Exhaustion

variable {μ : Measure E} {A₀ : NonUnitalSubalgebra ℝ (E → ℝ)} {u : ℕ → E → ℝ}

lemma IsExhaustion.monotone_ae (hu : IsExhaustion μ A₀ u) : ∀ᵐ x ∂μ, Monotone fun n => u n x := by
  filter_upwards [ae_all_iff.2 hu.2.1] with x hx
  exact monotone_nat_of_le_succ hx

lemma IsExhaustion.le_one_ae (hu : IsExhaustion μ A₀ u) : ∀ᵐ x ∂μ, ∀ n, u n x ≤ 1 := by
  filter_upwards [hu.monotone_ae, hu.2.2] with x h1 h2 n
  exact h1.ge_of_tendsto h2 n

lemma IsExhaustion.ge_zero_ae (hu : IsExhaustion μ A₀ u) : ∀ᵐ x ∂μ, ∀ n, u 0 x ≤ u n x := by
  filter_upwards [hu.monotone_ae] with x h1 n
  exact h1 (Nat.zero_le n)

end Exhaustion

namespace DiffusionTriple

variable (T : DiffusionTriple E)

/-- `P_t` is monotone (a.e.): a consequence of positivity. -/
theorem semigroup_mono (t : ℝ≥0) {a b : Lp ℝ 2 T.μ} (h : (a : E → ℝ) ≤ᵐ[T.μ] (b : E → ℝ)) :
    (T.semigroup t a : E → ℝ) ≤ᵐ[T.μ] (T.semigroup t b : E → ℝ) := by
  have h0 : 0 ≤ᵐ[T.μ] (b - a) := by
    filter_upwards [h, Lp.coeFn_sub b a] with x h1 h2
    simp only [Pi.zero_apply]; rw [h2]; simp only [Pi.sub_apply]; linarith
  have h1 := T.semigroup_nonneg t h0
  have e : T.semigroup t (b - a) = T.semigroup t b - T.semigroup t a := map_sub _ _ _
  rw [e] at h1
  filter_upwards [h1, Lp.coeFn_sub (T.semigroup t b) (T.semigroup t a)] with x h2 h3
  simp only [Pi.zero_apply] at h2
  rw [h3] at h2
  simp only [Pi.sub_apply] at h2
  linarith

/-- `P_t u_n` for an exhaustion sequence. -/
noncomputable def exhP {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (t : ℝ≥0) (n : ℕ) :
    Lp ℝ 2 T.μ :=
  T.semigroup t (T.cls ⟨u n, hu.1 n⟩)

lemma cls_mono_ae {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (n : ℕ) :
    (T.cls ⟨u n, hu.1 n⟩ : E → ℝ) ≤ᵐ[T.μ] (T.cls ⟨u (n + 1), hu.1 (n + 1)⟩ : E → ℝ) := by
  filter_upwards [coeFn_cls T ⟨u n, hu.1 n⟩, coeFn_cls T ⟨u (n + 1), hu.1 (n + 1)⟩, hu.2.1 n]
    with x h1 h2 h3
  rw [h1, h2]; exact h3

lemma cls_le_one_ae {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (n : ℕ) :
    (T.cls ⟨u n, hu.1 n⟩ : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ) := by
  filter_upwards [coeFn_cls T ⟨u n, hu.1 n⟩, hu.le_one_ae] with x h1 h2
  rw [h1]; exact h2 n

theorem exhP_monotone_ae {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, Monotone fun n => (T.exhP hu t n : E → ℝ) x := by
  have : ∀ n, ∀ᵐ x ∂T.μ, (T.exhP hu t n : E → ℝ) x ≤ (T.exhP hu t (n + 1) : E → ℝ) x :=
    fun n => T.semigroup_mono t (T.cls_mono_ae hu n)
  filter_upwards [ae_all_iff.2 this] with x hx
  exact monotone_nat_of_le_succ hx

theorem exhP_le_one_ae {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, ∀ n, (T.exhP hu t n : E → ℝ) x ≤ 1 := by
  have : ∀ n, ∀ᵐ x ∂T.μ, (T.exhP hu t n : E → ℝ) x ≤ 1 := fun n =>
    T.semigroup_le_one t _ (T.cls_le_one_ae hu n)
  exact ae_all_iff.2 this

/-! ### Comparison of two exhaustion sequences -/

/-- `(v − u)⁺`. -/
def posdiff (v u : E → ℝ) : E → ℝ := fun x => max (v x - u x) 0

lemma memLp_posdiff {v u : E → ℝ} (hv : MemLp v 2 T.μ) (hu : MemLp u 2 T.μ) :
    MemLp (posdiff v u) 2 T.μ := by
  refine (hv.sub hu).of_le
    (((hv.aemeasurable.sub hu.aemeasurable).max aemeasurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [posdiff, Pi.sub_apply, Real.norm_eq_abs]
  rcases le_total (v x - u x) 0 with h | h
  · rw [max_eq_right h]; simp
  · rw [max_eq_left h]

theorem comparison {u v : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u) (hv : IsExhaustion T.μ T.A₀ v)
    (t : ℝ≥0) (m : ℕ) :
    ∀ᵐ x ∂T.μ, ∀ ℓ : ℝ, Tendsto (fun n => (T.exhP hu t n : E → ℝ) x) atTop (𝓝 ℓ) →
      (T.exhP hv t m : E → ℝ) x ≤ ℓ := by
  have hvm := memLp2 T (hv.1 m)
  have hW : ∀ n, MemLp (posdiff (v m) (u n)) 2 T.μ := fun n =>
    memLp_posdiff T hvm (memLp2 T (hu.1 n))
  set W : ℕ → Lp ℝ 2 T.μ := fun n => (hW n).toLp _ with hWdef
  have hWc : ∀ n, (W n : E → ℝ) =ᵐ[T.μ] posdiff (v m) (u n) := fun n => (hW n).coeFn_toLp
  -- `‖W n‖ → 0`
  have hsq : ∀ n, ‖W n‖ ^ 2 = ∫ x, (posdiff (v m) (u n) x) ^ 2 ∂T.μ := by
    intro n
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hWc n] with x hx
    rw [hx]; simp [sq]
  have hbd : Integrable (fun x => (|v m x| + |u 0 x|) ^ 2) T.μ :=
    ((hvm.norm.add (memLp2 T (hu.1 0)).norm)).integrable_sq.congr
      (Filter.Eventually.of_forall fun x => by simp)
  have hlim : Tendsto (fun n => ∫ x, (posdiff (v m) (u n) x) ^ 2 ∂T.μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := T.μ)
      (fun x => (|v m x| + |u 0 x|) ^ 2)
      (F := fun n x => (posdiff (v m) (u n) x) ^ 2) (f := fun _ => (0 : ℝ))
      (fun n => ((hW n).aemeasurable.pow_const 2).aestronglyMeasurable) hbd
      (fun n => by
        filter_upwards [hu.ge_zero_ae] with x hx
        have h0 : 0 ≤ posdiff (v m) (u n) x := le_max_right _ _
        have h1 : posdiff (v m) (u n) x ≤ |v m x| + |u 0 x| := by
          simp only [posdiff]
          refine max_le ?_ (by positivity)
          have := hx n
          have := le_abs_self (v m x)
          have := neg_abs_le (u 0 x)
          linarith
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ h0 h1 2)
      (by
        filter_upwards [hu.2.2, hv.le_one_ae] with x hx hv1
        have h1 : Tendsto (fun n => max (v m x - u n x) 0) atTop (𝓝 (max (v m x - 1) 0)) :=
          (tendsto_const_nhds.sub hx).max tendsto_const_nhds
        have h2 : max (v m x - 1) 0 = 0 := max_eq_right (by linarith [hv1 m])
        rw [h2] at h1
        simpa [posdiff] using h1.pow 2)
    simpa using this
  have hnorm : Tendsto (fun n => ‖W n‖) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => ‖W n‖ ^ 2) atTop (𝓝 0) := by
      simpa only [hsq] using hlim
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h3
    exact h3.congr (fun n => by simp [Real.sqrt_sq (norm_nonneg _)])
  have hPW : Tendsto (fun n => T.semigroup t (W n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hnorm
    calc ‖T.semigroup t (W n)‖ ≤ ‖T.semigroup t‖ * ‖W n‖ := (T.semigroup t).le_opNorm _
      _ ≤ 1 * ‖W n‖ := mul_le_mul_of_nonneg_right
        ((formData T).norm_semigroup_le t) (norm_nonneg _)
      _ = ‖W n‖ := one_mul _
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hPW).exists_seq_tendsto_ae
  -- pointwise inequality `P_t v_m ≤ P_t u_n + P_t W_n`
  have hineq : ∀ n, ∀ᵐ x ∂T.μ, (T.exhP hv t m : E → ℝ) x ≤
      (T.exhP hu t n : E → ℝ) x + (T.semigroup t (W n) : E → ℝ) x := by
    intro n
    have hle : (T.cls ⟨v m, hv.1 m⟩ : E → ℝ) ≤ᵐ[T.μ]
        (T.cls ⟨u n, hu.1 n⟩ + W n : Lp ℝ 2 T.μ) := by
      filter_upwards [coeFn_cls T ⟨v m, hv.1 m⟩, coeFn_cls T ⟨u n, hu.1 n⟩, hWc n,
        Lp.coeFn_add (T.cls ⟨u n, hu.1 n⟩) (W n)] with x h1 h2 h3 h4
      rw [h1, h4, Pi.add_apply, h2, h3]
      simp only [posdiff]
      linarith [le_max_left (v m x - u n x) 0]
    have := T.semigroup_mono t hle
    have e : T.semigroup t (T.cls ⟨u n, hu.1 n⟩ + W n) =
        T.semigroup t (T.cls ⟨u n, hu.1 n⟩) + T.semigroup t (W n) := map_add _ _ _
    rw [e] at this
    filter_upwards [this, Lp.coeFn_add (T.semigroup t (T.cls ⟨u n, hu.1 n⟩)) (T.semigroup t (W n))]
      with x h1 h2
    rw [h2] at h1
    exact h1
  filter_upwards [ae_all_iff.2 hineq, hae, Lp.coeFn_zero ℝ 2 T.μ] with x hx hx2 hz
  intro ℓ hℓ
  have h0 : Tendsto (fun i => (T.semigroup t (W (ns i)) : E → ℝ) x) atTop (𝓝 0) := by
    rw [hz] at hx2; exact hx2
  have h1 := (hℓ.comp hns.tendsto_atTop).add h0
  rw [add_zero] at h1
  exact ge_of_tendsto' h1 (fun i => hx (ns i))

/-- **Independence of the exhaustion sequence.**  If `P_t v_n → 1` a.e. for one exhaustion sequence
`v`, then `P_t u_n → 1` a.e. for every exhaustion sequence `u` (signs arbitrary). -/
theorem conservative_transfer {u v : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u)
    (hv : IsExhaustion T.μ T.A₀ v) (t : ℝ≥0)
    (h : ∀ᵐ x ∂T.μ, Tendsto (fun n => (T.exhP hv t n : E → ℝ) x) atTop (𝓝 1)) :
    ∀ᵐ x ∂T.μ, Tendsto (fun n => (T.exhP hu t n : E → ℝ) x) atTop (𝓝 1) := by
  filter_upwards [T.exhP_monotone_ae hu t, T.exhP_le_one_ae hu t, ae_all_iff.2 (T.comparison hu hv t),
    h] with x hmono hle hcmp hv1
  have hbdd : BddAbove (Set.range fun n => (T.exhP hu t n : E → ℝ) x) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact hle n⟩
  have hl := tendsto_atTop_ciSup hmono hbdd
  have h1 : (1 : ℝ) ≤ ⨆ n, (T.exhP hu t n : E → ℝ) x :=
    le_of_tendsto' hv1 (fun m => hcmp m _ hl)
  have h2 : (⨆ n, (T.exhP hu t n : E → ℝ) x) ≤ 1 := ciSup_le hle
  have : (⨆ n, (T.exhP hu t n : E → ℝ) x) = 1 := le_antisymm h2 h1
  rwa [this] at hl

/-! ### Existence of nonnegative exhaustion sequences -/

theorem exists_nonneg_exhaustion :
    ∃ u : ℕ → E → ℝ, IsExhaustion T.μ T.A₀ u ∧ ∀ n x, 0 ≤ u n x := by
  obtain ⟨u, hu1, hu2, hu3⟩ := T.exhaustion
  set ψ : (Fin 1 → ℝ) → ℝ := fun z => Real.smoothTransition (z 0) with hψ
  have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ 0)
  have hψ0 : ψ 0 = 0 := by simp [hψ, Real.smoothTransition.zero_of_nonpos]
  refine ⟨fun n x => Real.smoothTransition (u n x), ⟨fun n => ?_, fun n => ?_, ?_⟩,
    fun n x => Real.smoothTransition.nonneg _⟩
  · exact T.comp_mem 1 ψ hψc hψ0 (fun _ => u n) (fun _ => hu1 n)
  · filter_upwards [hu2 n] with x hx
    exact Real.smoothTransition.monotone hx
  · filter_upwards [hu3] with x hx
    have h1 := (Real.smoothTransition.contDiff (n := 0)).continuous.tendsto 1 |>.comp hx
    have h2 : Real.smoothTransition 1 = 1 := Real.smoothTransition.one_of_one_le le_rfl
    rw [h2] at h1
    exact h1

end DiffusionTriple

namespace StandardTriple

/-- **S11 for every exhaustion sequence** (signed or not): the field `conservative` is stated for
nonnegative exhaustion sequences only; by independence it holds for all of them. -/
theorem conservative_all (S : StandardTriple E) {u : ℕ → E → ℝ}
    (hu : IsExhaustion S.μ S.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂S.μ, Tendsto (fun n => (S.toDiffusionTriple.exhP hu t n : E → ℝ) x) atTop (𝓝 1) := by
  obtain ⟨v, hv, hv0⟩ := S.toDiffusionTriple.exists_nonneg_exhaustion
  exact S.toDiffusionTriple.conservative_transfer hu hv t
    (S.conservative v hv (fun n => Filter.Eventually.of_forall (hv0 n)) t)

end StandardTriple

end MarkovTriple.BGL
