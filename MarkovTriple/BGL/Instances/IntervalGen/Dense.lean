import Mathlib
import MarkovTriple.BGL.Instances.IntervalGen.Basic

/-!
# Density of `C_c^∞(Ω)` in `Lᵖ(Ω, μ)` for bounded open `Ω ⊆ ℝ`

See `STATEMENTS_R22_E1.md` (G1).  Mathlib approximation by `C_c^∞(ℝ)`, then multiplication by the cut-off
`θ_n` (`= 1` on `K n`); the error is `≤ ‖g‖_∞ μ(Ω ∖ K n)^{1/p} → 0`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.IntervalGen

namespace BddOpen

variable (Ω : BddOpen)

/-- `S n = Ω ∖ K n`. -/
def S (n : ℕ) : Set ℝ := Ω.carrier ∩ (Ω.K n)ᶜ

lemma measurableSet_S (n : ℕ) : MeasurableSet (Ω.S n) :=
  Ω.isOpen.measurableSet.inter (Ω.isClosed_K n).measurableSet.compl

lemma tendsto_S : Tendsto (fun n => Ω.μ (Ω.S n)) atTop (𝓝 0) := by
  have hanti : Antitone Ω.S := by
    refine antitone_nat_of_succ_le fun n x hx => ⟨hx.1, fun hK => hx.2 ?_⟩
    have hK' : 1 / ((n : ℝ) + 1) ≤ Metric.infDist x Ω.carrierᶜ := hK
    have h2 : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    exact h2.trans hK'
  have h := tendsto_measure_iInter_atTop (μ := Ω.μ) (fun n => (Ω.measurableSet_S n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n, Ω.S n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have hxΩ : x ∈ Ω.carrier := (Set.mem_iInter.1 hx 0).1
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (Ω.pos_dist hxΩ)
    exact (Set.mem_iInter.1 hx N).2 (show 1 / ((N : ℝ) + 1) ≤ _ from hN.le)
  rw [hempty, measure_empty] at h
  exact h

theorem A₀_dense (p : ℝ≥0∞) [hp1 : Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p Ω.μ | ∃ f ∈ Ω.A₀, (u : ℝ → ℝ) =ᵐ[Ω.μ] f} := by
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1.out).ne'
  obtain ⟨g, hgcs, hgcd, hg⟩ := MemLp.exist_eLpNorm_sub_le hp hp1.out (Lp.memLp u) (half_pos hε)
  have hgs : Lebesgue.Sm g := hgcd
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgcs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have t2 : Tendsto (fun n : ℕ => Ω.μ (Ω.S n)) atTop (𝓝 0) := Ω.tendsto_S
  have t3 : Tendsto (fun n : ℕ => Ω.μ (Ω.S n) ^ (1 / p.toReal)) atTop (𝓝 0) := by
    have hptoReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    have := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp t2
    rwa [ENNReal.zero_rpow_of_pos (by positivity)] at this
  have t4 : Tendsto (fun n : ℕ => ENNReal.ofReal C * Ω.μ (Ω.S n) ^ (1 / p.toReal)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul t3 (Or.inr ENNReal.ofReal_ne_top)
  obtain ⟨n, hn⟩ := (t4.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))).exists
  set θ := Ω.cut n with hθ
  set g' : ℝ → ℝ := fun x => θ x * g x with hg'
  have hg'mem : g' ∈ Ω.A₀ :=
    ⟨(Ω.cut_smooth n).mul hgs,
      (tsupport_mul_subset_left (f := θ) (g := g)).trans (Ω.cut_tsupport n)⟩
  have hg'Lp : MemLp g' p Ω.μ :=
    (A₀_smooth hg'mem).continuous.memLp_of_hasCompactSupport (A₀_cs hg'mem)
  set h : ℝ → ℝ := fun x => (1 - θ x) * g x with hh
  have hcont : Continuous h := ((contDiff_const.sub (Ω.cut_smooth n)).mul hgs).continuous
  have hbound : ∀ᵐ x ∂Ω.μ, ‖h x‖ ≤ ‖(Ω.S n).indicator (fun _ => C) x‖ := by
    refine (Ω.ae_μ_iff).2 (Filter.Eventually.of_forall fun x hx => ?_)
    by_cases hxS : x ∈ Ω.S n
    · rw [indicator_of_mem hxS, Real.norm_of_nonneg hC0]
      have h1 : |1 - θ x| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [(Ω.cut_range n x).2])]; linarith [(Ω.cut_range n x).1]
      calc ‖h x‖ = |1 - θ x| * ‖g x‖ := by simp [hh]
        _ ≤ 1 * C := mul_le_mul h1 (hC x) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · have hK : x ∈ Ω.K n := by
        by_contra hK; exact hxS ⟨hx, hK⟩
      have : θ x = 1 := Ω.cut_eq_one hK
      simp [hh, this]
  have hhnorm : eLpNorm h p Ω.μ ≤ ENNReal.ofReal (ε / 2) := by
    calc eLpNorm h p Ω.μ ≤ eLpNorm ((Ω.S n).indicator fun _ => C) p Ω.μ :=
          eLpNorm_mono_ae hcont.aestronglyMeasurable hbound
      _ = ‖C‖ₑ * Ω.μ (Ω.S n) ^ (1 / p.toReal) :=
          eLpNorm_indicator_const (Ω.measurableSet_S n).nullMeasurableSet hp0 hp
      _ = ENNReal.ofReal C * Ω.μ (Ω.S n) ^ (1 / p.toReal) := by rw [Real.enorm_eq_ofReal hC0]
      _ ≤ _ := hn
  have hu_sub : eLpNorm ((u : ℝ → ℝ) - g') p Ω.μ ≤ ENNReal.ofReal ε := by
    have e : (u : ℝ → ℝ) - g' = ((u : ℝ → ℝ) - g) + h := by
      funext x; simp only [hg', hh, Pi.sub_apply, Pi.add_apply]; ring
    rw [e]
    calc _ ≤ eLpNorm ((u : ℝ → ℝ) - g) p Ω.μ + eLpNorm h p Ω.μ :=
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

end BddOpen

end MarkovTriple.BGL.Instances.IntervalGen
