import Mathlib
import MarkovTriple.BGL.Instances.Interval.Basic

/-!
# Zonal Gegenbauer `λ = 3/2` on `(-1,1)`: measure, algebra `C_c^∞((-1,1))`, cut-offs, density

See `STATEMENTS_R22_E2.md`.  `μ = (3/4)(1-x²) dx` on `(-1,1)`; `𝒜₀ = {f smooth, tsupport f ⊆ (-1,1)}`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open MarkovTriple.BGL.Instances.Interval

/-- `(3/4)(1-x²) dx` on `(-1,1)`, as a measure on `ℝ`. -/
noncomputable abbrev goμ : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (3 / 4 * (1 - x ^ 2)))

lemma measurable_goρ : Measurable (fun x : ℝ => ENNReal.ofReal (3 / 4 * (1 - x ^ 2))) := by fun_prop

lemma goμ_le : goμ ≤ volume.restrict (Ioo (-1 : ℝ) 1) := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [withDensity_apply _ hs]
  calc ∫⁻ a in s, ENNReal.ofReal (3 / 4 * (1 - a ^ 2)) ∂(volume.restrict (Ioo (-1 : ℝ) 1))
      ≤ ∫⁻ _ in s, 1 ∂(volume.restrict (Ioo (-1 : ℝ) 1)) := by
        refine lintegral_mono fun a => ?_
        rw [ENNReal.ofReal_le_one]; nlinarith [sq_nonneg a]
    _ = _ := by simp

lemma goμ_le_volume : goμ ≤ volume :=
  goμ_le.trans Measure.restrict_le_self

/-- integrals against `goμ` of functions vanishing off `(-1,1)`. -/
lemma integral_goμ {h : ℝ → ℝ} (hh : ∀ x ∉ Ioo (-1 : ℝ) 1, h x = 0) :
    ∫ x, h x ∂goμ = ∫ x, (3 / 4 * (1 - x ^ 2)) * h x := by
  have e : ∫ x, h x ∂goμ = ∫ x, (Real.toNNReal (3 / 4 * (1 - x ^ 2))) • h x
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)) :=
    integral_withDensity_eq_integral_smul (f := fun x => Real.toNNReal (3 / 4 * (1 - x ^ 2)))
      (by fun_prop) h
  rw [e]
  have e2 : ∫ x, (Real.toNNReal (3 / 4 * (1 - x ^ 2))) • h x ∂(volume.restrict (Ioo (-1 : ℝ) 1))
      = ∫ x, (Real.toNNReal (3 / 4 * (1 - x ^ 2))) • h x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hh x hx]
  rw [e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · have : 0 ≤ 3 / 4 * (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
    simp [NNReal.smul_def, Real.coe_toNNReal _ this]
  · simp [hh x hx]

instance isProb_goμ : IsProbabilityMeasure goμ := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · have : ∫ x in Ioo (-1 : ℝ) 1, 3 / 4 * (1 - x ^ 2) = 1 := by
      rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le (by norm_num)]
      have hd : ∀ x ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun x : ℝ => 3 / 4 * (x - x ^ 3 / 3))
          (3 / 4 * (1 - x ^ 2)) x := fun x _ => by
        have := (((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3))).const_mul (3 / 4 : ℝ)
        convert this using 1
        simp; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((by fun_prop : Continuous fun x : ℝ => 3 / 4 * (1 - x ^ 2)).intervalIntegrable _ _)]
      norm_num
    rw [this]; simp
  · exact (by fun_prop : Continuous fun x : ℝ => 3 / 4 * (1 - x ^ 2)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
    simp only [Pi.zero_apply]
    nlinarith [hx.1, hx.2]

/-! ### The algebra `C_c^∞((-1,1))` -/

/-- `C_c^∞((-1,1))`. -/
def goA₀ : NonUnitalSubalgebra ℝ (ℝ → ℝ) where
  carrier := {f | Lebesgue.Sm f ∧ tsupport f ⊆ Ioo (-1) 1}
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, tsupport_add_sub.trans (union_subset hf.2 hg.2)⟩
  zero_mem' := ⟨contDiff_const, by simp⟩
  mul_mem' := fun {f g} hf hg => ⟨hf.1.mul hg.1, tsupport_mul_subset_left.trans hf.2⟩
  smul_mem' := fun c {f} hf =>
    ⟨hf.1.const_smul c, (tsupport_smul_subset_right (fun _ => c) f).trans hf.2⟩

lemma mem_goA₀ {f : ℝ → ℝ} : f ∈ goA₀ ↔ Lebesgue.Sm f ∧ tsupport f ⊆ Ioo (-1) 1 := Iff.rfl

lemma goA₀_smooth {f : ℝ → ℝ} (hf : f ∈ goA₀) : Lebesgue.Sm f := hf.1

lemma goA₀_cs {f : ℝ → ℝ} (hf : f ∈ goA₀) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) (hf.2.trans Ioo_subset_Icc_self)

lemma goA₀_le {f : ℝ → ℝ} (hf : f ∈ goA₀) : f ∈ Lebesgue.A₀ :=
  Lebesgue.mem_A₀.2 ⟨hf.1, goA₀_cs hf⟩

lemma deriv_mem_goA₀ {f : ℝ → ℝ} (hf : f ∈ goA₀) : deriv f ∈ goA₀ :=
  ⟨hf.1.deriv', (tsupport_deriv_subset (f := f)).trans hf.2⟩

lemma zero_off_go {f : ℝ → ℝ} (hf : f ∈ goA₀) {x : ℝ} (hx : x ∉ Ioo (-1 : ℝ) 1) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hf.2 h))

/-- multiplying by a smooth function: `p · f` for smooth `p` and `f ∈ 𝒜₀`. -/
lemma smul_mem_goA₀ {p f : ℝ → ℝ} (hp : Lebesgue.Sm p) (hf : f ∈ goA₀) :
    (fun x => p x * f x) ∈ goA₀ :=
  ⟨hp.mul hf.1, (tsupport_mul_subset_right (f := p) (g := f)).trans hf.2⟩

lemma comp_mem_goA₀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ goA₀) : (fun x => ψ (fun i => f i x)) ∈ goA₀ := by
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

/-- `u_n(x) = ivcut n ((x+1)/2)`. -/
noncomputable def gocut (n : ℕ) (x : ℝ) : ℝ := ivcut n ((x + 1) / 2)

lemma gocut_smooth (n : ℕ) : Lebesgue.Sm (gocut n) :=
  (ivcut_smooth n).comp ((contDiff_id.add contDiff_const).div_const 2)

lemma gocut_tsupport (n : ℕ) : tsupport (gocut n) ⊆ Ioo (-1) 1 := by
  have hc : Continuous fun x : ℝ => (x + 1) / 2 := by fun_prop
  have h1 : Function.support (gocut n) ⊆ (fun x : ℝ => (x + 1) / 2) ⁻¹' tsupport (ivcut n) :=
    fun x hx => subset_closure hx
  refine (closure_minimal h1 ((isClosed_tsupport _).preimage hc)).trans ?_
  intro x hx
  have := ivcut_tsupport n hx
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

lemma gocut_mem (n : ℕ) : gocut n ∈ goA₀ := ⟨gocut_smooth n, gocut_tsupport n⟩

lemma gocut_nonneg (n : ℕ) (x : ℝ) : 0 ≤ gocut n x := ivcut_nonneg n _

lemma gocut_le_one (n : ℕ) (x : ℝ) : gocut n x ≤ 1 := ivcut_le_one n _

lemma gocut_mono (n : ℕ) (x : ℝ) : gocut n x ≤ gocut (n + 1) x := ivcut_mono n _

lemma gocut_tendsto {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun n => gocut n x) atTop (𝓝 1) :=
  ivcut_tendsto ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma gocut_mul_mem {g : ℝ → ℝ} (hg : Lebesgue.Sm g) (n : ℕ) :
    (fun x => gocut n x * g x) ∈ goA₀ :=
  ⟨(gocut_smooth n).mul hg,
    (tsupport_mul_subset_left (f := gocut n) (g := g)).trans (gocut_tsupport n)⟩

/-- off the two end layers of width `4/(n+1)`, the cut-off equals `1`. -/
lemma gocut_eq_one {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hxS : x ∉ Ioc (-1) (-1 + 4 / ((n : ℝ) + 1)) ∪ Ico (1 - 4 / ((n : ℝ) + 1)) 1) :
    gocut n x = 1 := by
  refine ivcut_eq_one (n := n) ⟨by linarith [hx.1], by linarith [hx.2]⟩ ?_
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · refine hxS (Or.inl ⟨hx.1, ?_⟩)
    have : 2 / ((n : ℝ) + 1) * 2 = 4 / ((n : ℝ) + 1) := by ring
    linarith
  · refine hxS (Or.inr ⟨?_, hx.2⟩)
    have : 2 / ((n : ℝ) + 1) * 2 = 4 / ((n : ℝ) + 1) := by ring
    linarith

/-! ### Density in `Lᵖ(μ)` -/

theorem goA₀_dense (p : ℝ≥0∞) [hp1 : Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p goμ | ∃ f ∈ goA₀, (u : ℝ → ℝ) =ᵐ[goμ] f} := by
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1.out).ne'
  have hptoReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨g, hgcs, hgcd, hg⟩ := MemLp.exist_eLpNorm_sub_le hp hp1.out (Lp.memLp u) (half_pos hε)
  have hgs : Lebesgue.Sm g := hgcd
  have hgmem : MemLp g p goμ := hgs.continuous.memLp_of_hasCompactSupport hgcs
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgcs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have t1 : Tendsto (fun n : ℕ => (8 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 8
  have t2 : Tendsto (fun n : ℕ => ENNReal.ofReal ((8 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal t1
  have t3 : Tendsto (fun n : ℕ => ENNReal.ofReal ((8 : ℝ) / ((n : ℝ) + 1)) ^ (1 / p.toReal))
      atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp t2
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at this
  have t4 : Tendsto (fun n : ℕ => ENNReal.ofReal C *
      ENNReal.ofReal ((8 : ℝ) / ((n : ℝ) + 1)) ^ (1 / p.toReal)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul t3 (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨n, hn⟩ := (t4.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))).exists
  set θ := gocut n with hθ
  set g' : ℝ → ℝ := fun x => θ x * g x with hg'
  have hg'mem : g' ∈ goA₀ := gocut_mul_mem hgs n
  have hg'Lp : MemLp g' p goμ :=
    ((Lebesgue.memLp_of (goA₀_le hg'mem) p).mono_measure goμ_le_volume)
  set h : ℝ → ℝ := fun x => (1 - θ x) * g x with hh
  have hcont : Continuous h := ((contDiff_const.sub (gocut_smooth n)).mul hgs).continuous
  set S : Set ℝ := Ioc (-1) (-1 + 4 / ((n : ℝ) + 1)) ∪ Ico (1 - 4 / ((n : ℝ) + 1)) 1 with hS
  have hSm : MeasurableSet S := measurableSet_Ioc.union measurableSet_Ico
  have hSvol : volume S ≤ ENNReal.ofReal ((8 : ℝ) / ((n : ℝ) + 1)) := by
    refine (measure_union_le _ _).trans ?_
    have e : 1 - (1 - 4 / ((n : ℝ) + 1)) = 4 / ((n : ℝ) + 1) := by ring
    have e' : -1 + 4 / ((n : ℝ) + 1) - -1 = 4 / ((n : ℝ) + 1) := by ring
    rw [Real.volume_Ioc, Real.volume_Ico, e, e',
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : (8 : ℝ) / ((n : ℝ) + 1) = 4 / ((n : ℝ) + 1) + 4 / ((n : ℝ) + 1) := by ring
    rw [this]
  have hbound : ∀ᵐ x ∂goμ, ‖h x‖ ≤ ‖S.indicator (fun _ => C) x‖ := by
    have hae : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), ‖h x‖ ≤ ‖S.indicator (fun _ => C) x‖ :=
      (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => by
        by_cases hxS : x ∈ S
        · rw [indicator_of_mem hxS, Real.norm_of_nonneg hC0]
          have h1 : |1 - θ x| ≤ 1 := by
            rw [abs_of_nonneg (by linarith [gocut_le_one n x])]; linarith [gocut_nonneg n x]
          calc ‖h x‖ = |1 - θ x| * ‖g x‖ := by simp [hh]
            _ ≤ 1 * C := mul_le_mul h1 (hC x) (norm_nonneg _) zero_le_one
            _ = C := one_mul C
        · have : θ x = 1 := gocut_eq_one hx hxS
          simp [hh, this])
    exact Measure.absolutelyContinuous_of_le goμ_le hae
  have hhnorm : eLpNorm h p goμ ≤ ENNReal.ofReal (ε / 2) := by
    calc eLpNorm h p goμ ≤ eLpNorm (S.indicator fun _ => C) p goμ :=
          eLpNorm_mono_ae hcont.aestronglyMeasurable hbound
      _ = ‖C‖ₑ * goμ S ^ (1 / p.toReal) := eLpNorm_indicator_const hSm.nullMeasurableSet hp0 hp
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((8 : ℝ) / ((n : ℝ) + 1)) ^ (1 / p.toReal) := by
          gcongr
          · exact (Real.enorm_eq_ofReal hC0).le
          · exact (Measure.le_iff'.1 goμ_le_volume S).trans hSvol
      _ ≤ _ := hn
  have hu_sub : eLpNorm ((u : ℝ → ℝ) - g') p goμ ≤ ENNReal.ofReal ε := by
    have e : (u : ℝ → ℝ) - g' = ((u : ℝ → ℝ) - g) + h := by
      funext x; simp only [hg', hh, Pi.sub_apply, Pi.add_apply]; ring
    rw [e]
    calc _ ≤ eLpNorm ((u : ℝ → ℝ) - g) p goμ + eLpNorm h p goμ :=
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

end MarkovTriple.BGL.Instances.GegenbauerOpen
