import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Basic

/-!
# The interval triple on `(0,1)`: the algebra `𝒜₀ = C_c^∞((0,1))`, cut-offs and density

State space `ℝ`, `μ = volume.restrict (Ioo 0 1)`; `𝒜₀ = {f smooth, tsupport f ⊆ (0,1)}`.
See `STATEMENTS_R21_Interval.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.Interval

/-- Lebesgue measure on `(0,1)` (a probability measure), as a measure on `ℝ`. -/
noncomputable abbrev ivμ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

lemma tsupport_add_sub {f g : ℝ → ℝ} : tsupport (f + g) ⊆ tsupport f ∪ tsupport g :=
  closure_minimal ((Function.support_add f g).trans (union_subset_union subset_closure subset_closure))
    ((isClosed_tsupport f).union (isClosed_tsupport g))

/-- `C_c^∞((0,1))`: smooth functions whose topological support lies in `(0,1)`. -/
def ivA₀ : NonUnitalSubalgebra ℝ (ℝ → ℝ) where
  carrier := {f | Lebesgue.Sm f ∧ tsupport f ⊆ Ioo 0 1}
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, tsupport_add_sub.trans (union_subset hf.2 hg.2)⟩
  zero_mem' := ⟨contDiff_const, by simp⟩
  mul_mem' := fun {f g} hf hg => ⟨hf.1.mul hg.1, tsupport_mul_subset_left.trans hf.2⟩
  smul_mem' := fun c {f} hf =>
    ⟨hf.1.const_smul c, (tsupport_smul_subset_right (fun _ => c) f).trans hf.2⟩

lemma mem_ivA₀ {f : ℝ → ℝ} : f ∈ ivA₀ ↔ Lebesgue.Sm f ∧ tsupport f ⊆ Ioo 0 1 := Iff.rfl

lemma ivA₀_smooth {f : ℝ → ℝ} (hf : f ∈ ivA₀) : Lebesgue.Sm f := hf.1

lemma ivA₀_cs {f : ℝ → ℝ} (hf : f ∈ ivA₀) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) (hf.2.trans Ioo_subset_Icc_self)

lemma ivA₀_le {f : ℝ → ℝ} (hf : f ∈ ivA₀) : f ∈ Lebesgue.A₀ :=
  Lebesgue.mem_A₀.2 ⟨hf.1, ivA₀_cs hf⟩

lemma deriv_mem_ivA₀ {f : ℝ → ℝ} (hf : f ∈ ivA₀) : deriv f ∈ ivA₀ :=
  ⟨hf.1.deriv', (tsupport_deriv_subset (f := f)).trans hf.2⟩

lemma comp_mem_ivA₀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ ivA₀) : (fun x => ψ (fun i => f i x)) ∈ ivA₀ := by
  refine ⟨Lebesgue.comp_sm ψ hψ f (fun i => (hf i).1), ?_⟩
  have hsub : Function.support (fun x => ψ (fun i => f i x)) ⊆ ⋃ i, tsupport (f i) := by
    intro x hx
    by_contra hxx
    apply hx
    have : ∀ i, f i x = 0 := fun i =>
      image_eq_zero_of_notMem_tsupport (fun h => hxx (Set.mem_iUnion.2 ⟨i, h⟩))
    have e : (fun i => f i x) = 0 := funext this
    simp only [e, h0]
  refine (closure_minimal hsub (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)).trans ?_
  exact iUnion_subset fun i => (hf i).2

/-! ### The exhaustion sequence -/

/-- `u_n(x) = ST((n+1)x - 1) · ST((n+1)(1-x) - 1)` (`ST` the smooth step): smooth, `0 ≤ u_n ≤ 1`,
supported in `[1/(n+1), 1 - 1/(n+1)]`, equal to `1` on `[2/(n+1), 1 - 2/(n+1)]`. -/
noncomputable def ivcut (n : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * x - 1) *
    Real.smoothTransition (((n : ℝ) + 1) * (1 - x) - 1)

lemma ivcut_smooth (n : ℕ) : Lebesgue.Sm (ivcut n) := by
  unfold ivcut
  refine (Real.smoothTransition.contDiff.comp ?_).mul (Real.smoothTransition.contDiff.comp ?_)
  · exact (contDiff_const.mul contDiff_id).sub contDiff_const
  · exact (contDiff_const.mul (contDiff_const.sub contDiff_id)).sub contDiff_const

lemma ivcut_tsupport (n : ℕ) : tsupport (ivcut n) ⊆ Ioo 0 1 := by
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h : Function.support (ivcut n) ⊆ Icc (1 / ((n : ℝ) + 1)) (1 - 1 / ((n : ℝ) + 1)) := by
    intro x hx
    have h1 := left_ne_zero_of_mul hx
    have h2 := right_ne_zero_of_mul hx
    have a : 0 < ((n : ℝ) + 1) * x - 1 := by
      by_contra h
      exact h1 (Real.smoothTransition.zero_of_nonpos (not_lt.1 h))
    have b : 0 < ((n : ℝ) + 1) * (1 - x) - 1 := by
      by_contra h
      exact h2 (Real.smoothTransition.zero_of_nonpos (not_lt.1 h))
    constructor
    · rw [div_le_iff₀ hn]; nlinarith
    · have : 1 / ((n : ℝ) + 1) ≤ 1 - x := by rw [div_le_iff₀ hn]; nlinarith
      linarith
  refine (closure_minimal h isClosed_Icc).trans ?_
  rintro x ⟨h1, h2⟩
  exact ⟨by linarith, by linarith⟩

lemma ivcut_mem (n : ℕ) : ivcut n ∈ ivA₀ := ⟨ivcut_smooth n, ivcut_tsupport n⟩

lemma ivcut_nonneg (n : ℕ) (x : ℝ) : 0 ≤ ivcut n x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma ivcut_le_one (n : ℕ) (x : ℝ) : ivcut n x ≤ 1 :=
  calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (Real.smoothTransition.le_one _)
        (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma ivcut_mono (n : ℕ) (x : ℝ) : ivcut n x ≤ ivcut (n + 1) x := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases le_or_gt x 0 with hx | hx
  · have : ivcut n x = 0 := by
      unfold ivcut
      rw [Real.smoothTransition.zero_of_nonpos (by nlinarith), zero_mul]
    rw [this]; exact ivcut_nonneg _ _
  rcases le_or_gt 1 x with hx1 | hx1
  · have : ivcut n x = 0 := by
      unfold ivcut
      rw [Real.smoothTransition.zero_of_nonpos
        (x := ((n : ℝ) + 1) * (1 - x) - 1) (by nlinarith), mul_zero]
    rw [this]; exact ivcut_nonneg _ _
  unfold ivcut
  push_cast
  refine mul_le_mul (Real.smoothTransition.monotone ?_) (Real.smoothTransition.monotone ?_)
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · nlinarith
  · nlinarith

lemma ivcut_tendsto {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => ivcut n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / x)
  obtain ⟨M, hM⟩ := exists_nat_ge (2 / (1 - x))
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  filter_upwards [eventually_ge_atTop (max N M)] with n hn
  have hnN : 2 / x ≤ (n : ℝ) := hN.trans (by exact_mod_cast (le_max_left N M).trans hn)
  have hnM : 2 / (1 - x) ≤ (n : ℝ) := hM.trans (by exact_mod_cast (le_max_right N M).trans hn)
  have a : 2 ≤ (n : ℝ) * x := by rwa [div_le_iff₀ hx.1] at hnN
  have b : 2 ≤ (n : ℝ) * (1 - x) := by rwa [div_le_iff₀ hx1] at hnM
  unfold ivcut
  rw [Real.smoothTransition.one_of_one_le (by nlinarith [hx.1]),
    Real.smoothTransition.one_of_one_le (by nlinarith), mul_one]

/-! ### Density in `Lᵖ((0,1))` -/

lemma ivcut_mul_mem {g : ℝ → ℝ} (hg : Lebesgue.Sm g) (n : ℕ) :
    (fun x => ivcut n x * g x) ∈ ivA₀ :=
  ⟨(ivcut_smooth n).mul hg,
    (tsupport_mul_subset_left (f := ivcut n) (g := g)).trans (ivcut_tsupport n)⟩

/-- off `S_δ = (0, δ] ∪ [1-δ, 1)`, `δ = 2/(n+1)`, the cut-off equals `1` on `(0,1)`. -/
lemma ivcut_eq_one {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hxS : x ∉ Ioc 0 (2 / ((n : ℝ) + 1)) ∪ Ico (1 - 2 / ((n : ℝ) + 1)) 1) : ivcut n x = 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 2 / ((n : ℝ) + 1) < x := by
    by_contra h
    exact hxS (Or.inl ⟨hx.1, not_lt.1 h⟩)
  have h2 : x < 1 - 2 / ((n : ℝ) + 1) := by
    by_contra h
    exact hxS (Or.inr ⟨not_lt.1 h, hx.2⟩)
  have h3 : 2 / ((n : ℝ) + 1) < 1 - x := by linarith
  rw [div_lt_iff₀ hn] at h1 h3
  unfold ivcut
  rw [Real.smoothTransition.one_of_one_le (by nlinarith),
    Real.smoothTransition.one_of_one_le (by nlinarith), mul_one]

theorem ivA₀_dense (p : ℝ≥0∞) [hp1 : Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p ivμ | ∃ f ∈ ivA₀, (u : ℝ → ℝ) =ᵐ[ivμ] f} := by
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1.out).ne'
  have hptoReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨g, hgcs, hgcd, hg⟩ := MemLp.exist_eLpNorm_sub_le hp hp1.out (Lp.memLp u) (half_pos hε)
  have hgs : Lebesgue.Sm g := hgcd
  have hgmem : MemLp g p ivμ := hgs.continuous.memLp_of_hasCompactSupport hgcs
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgcs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- the tail estimate
  have t1 : Tendsto (fun n : ℕ => (4 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
  have t2 : Tendsto (fun n : ℕ => ENNReal.ofReal ((4 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal t1
  have t3 : Tendsto (fun n : ℕ => ENNReal.ofReal ((4 : ℝ) / ((n : ℝ) + 1)) ^ (1 / p.toReal))
      atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp t2
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at this
  have t4 : Tendsto (fun n : ℕ => ENNReal.ofReal C *
      ENNReal.ofReal ((4 : ℝ) / ((n : ℝ) + 1)) ^ (1 / p.toReal)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul t3 (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨n, hn⟩ := (t4.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))).exists
  set θ := ivcut n with hθ
  set g' : ℝ → ℝ := fun x => θ x * g x with hg'
  have hg'mem : g' ∈ ivA₀ := ivcut_mul_mem hgs n
  have hg'Lp : MemLp g' p ivμ := (Lebesgue.memLp_of (ivA₀_le hg'mem) p).restrict _
  -- the error term `h = (1 - θ) g`
  set h : ℝ → ℝ := fun x => (1 - θ x) * g x with hh
  have hcont : Continuous h := ((contDiff_const.sub (ivcut_smooth n)).mul hgs).continuous
  set S : Set ℝ := Ioc 0 (2 / ((n : ℝ) + 1)) ∪ Ico (1 - 2 / ((n : ℝ) + 1)) 1 with hS
  have hSm : MeasurableSet S := measurableSet_Ioc.union measurableSet_Ico
  have hSvol : volume S ≤ ENNReal.ofReal ((4 : ℝ) / ((n : ℝ) + 1)) := by
    refine (measure_union_le _ _).trans ?_
    have e : 1 - (1 - 2 / ((n : ℝ) + 1)) = 2 / ((n : ℝ) + 1) := by ring
    rw [Real.volume_Ioc, Real.volume_Ico, sub_zero, e,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : (4 : ℝ) / ((n : ℝ) + 1) = 2 / ((n : ℝ) + 1) + 2 / ((n : ℝ) + 1) := by ring
    rw [this]
  have hbound : ∀ᵐ x ∂ivμ, ‖h x‖ ≤ ‖S.indicator (fun _ => C) x‖ := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS, Real.norm_of_nonneg hC0]
      have h1 : |1 - θ x| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [ivcut_le_one n x])]; linarith [ivcut_nonneg n x]
      calc ‖h x‖ = |1 - θ x| * ‖g x‖ := by simp [hh]
        _ ≤ 1 * C := mul_le_mul h1 (hC x) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · have : θ x = 1 := ivcut_eq_one hx hxS
      simp [hh, this]
  have hhnorm : eLpNorm h p ivμ ≤ ENNReal.ofReal (ε / 2) := by
    calc eLpNorm h p ivμ ≤ eLpNorm (S.indicator fun _ => C) p ivμ := eLpNorm_mono_ae hcont.aestronglyMeasurable hbound
      _ = ‖C‖ₑ * ivμ S ^ (1 / p.toReal) := eLpNorm_indicator_const hSm.nullMeasurableSet hp0 hp
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((4 : ℝ) / ((n : ℝ) + 1)) ^ (1 / p.toReal) := by
          gcongr
          · exact (Real.enorm_eq_ofReal hC0).le
          · exact (Measure.le_iff'.1 Measure.restrict_le_self S).trans hSvol
      _ ≤ _ := hn
  have hu_sub : eLpNorm ((u : ℝ → ℝ) - g') p ivμ ≤ ENNReal.ofReal ε := by
    have e : (u : ℝ → ℝ) - g' = ((u : ℝ → ℝ) - g) + h := by
      funext x; simp only [hg', hh, Pi.sub_apply, Pi.add_apply]; ring
    rw [e]
    calc _ ≤ eLpNorm ((u : ℝ → ℝ) - g) p ivμ + eLpNorm h p ivμ :=
          eLpNorm_add_le hp1.out
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hg hhnorm
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  refine ⟨hg'Lp.toLp g', ⟨g', hg'mem, hg'Lp.coeFn_toLp⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← ENNReal.le_ofReal_iff_toReal_le ((Lp.memLp u).sub (Lp.memLp hg'Lp.toLp)).eLpNorm_ne_top hε.le]
  refine le_trans (le_of_eq ?_) hu_sub
  apply eLpNorm_congr_ae
  filter_upwards [hg'Lp.coeFn_toLp] with x h2
  simp only [Pi.sub_apply, h2]

end MarkovTriple.BGL.Instances.Interval
