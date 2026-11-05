import Mathlib
import MarkovTriple.Stochastic.R31U.Reverse
import MarkovTriple.Stochastic.R30T.Init

/-!
# Round 31 (U), part 4: Lipschitz smoothing of bounded data on `ℝ^d` (U2)

`reverse_poincare_sup` (`Γ(P_t h) ≤ C²/(2t)` a.e.) + local ellipticity + continuity/full support give `|∇ P_t h| ≤ C/√(2ct)`
everywhere on balls, for `h ∈ C_c^∞`; sup-norm approximation of `C_c` by `C_c^∞` (R30T) passes the bound to `C_c` data.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R31U

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R30T

variable {d : ℕ} (S : FullTriple (Rd d)) [IsFiniteMeasure S.toDiffusionTriple.μ]
  [S.toDiffusionTriple.μ.IsOpenPosMeasure]

/-- `L^∞`-to-Lipschitz bound for `C_c^∞` data, uniformly in the data. -/
theorem lip_smooth (hA : S.A = Afull d) (hCD : S.CD 0 ∞)
    (hell : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
      c * ∑ i, pderiv g i x ^ 2 ≤ S.toDiffusionTriple.ΓA g g x) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ≥0, 0 < t → ∀ (h : S.A₀) (C : ℝ), (∀ y, |h.1 y| ≤ C) →
      ∀ x y : Rd d, ‖x‖ < R → ‖y‖ < R →
        |S.Pt t h x - S.Pt t h y| ≤ K * C / Real.sqrt t * ‖x - y‖ := by
  obtain ⟨c, hc, hcell⟩ := hell R
  have h2c : 0 < 2 * c := by positivity
  refine ⟨d / Real.sqrt (2 * c), by positivity, fun t ht h C hC x y hx hy => ?_⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hts : 0 < Real.sqrt t := Real.sqrt_pos.2 (by exact_mod_cast ht)
  have hs2c : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.2 h2c
  set m : ℝ := C / Real.sqrt t / Real.sqrt (2 * c) with hm
  have hm0 : 0 ≤ m := by positivity
  set B : ℝ := C ^ 2 / (2 * t) with hB
  have hmB : m ^ 2 = B / c := by
    rw [hm, div_pow, div_pow, Real.sq_sqrt (by exact_mod_cast ht.le), Real.sq_sqrt h2c.le, hB]
    field_simp
  have hRP : ∀ᵐ z ∂S.toDiffusionTriple.μ, 2 * (t : ℝ) * S.toDiffusionTriple.ΓA (S.Pt t h) (S.Pt t h) z ≤ C ^ 2 :=
    reverse_poincare_sup' hCD h (C := C) (Eventually.of_forall hC) t ht
  have hgSm : Sm (S.Pt t h) := by
    have := S.Pt_mem_A t h
    rw [hA] at this
    exact mem_Afull.1 this
  set g := S.Pt t h with hg
  have hder : ∀ (i : Fin d) (y : Rd d), ‖y‖ < R → |pderiv g i y| ≤ m := by
    intro i y hy
    have hae : ∀ᵐ z ∂S.toDiffusionTriple.μ, ‖z‖ < R → c * ∑ i, pderiv g i z ^ 2 ≤ B := by
      filter_upwards [hRP] with z h1 hz
      have h3 := hcell g hgSm z hz.le
      have : S.toDiffusionTriple.ΓA g g z ≤ B := by
        rw [hB, le_div_iff₀ (by positivity)]; linarith
      exact h3.trans this
    have hcont : Continuous fun z : Rd d => c * ∑ i, pderiv g i z ^ 2 := by
      refine continuous_const.mul (continuous_finsetSum _ fun j _ => ?_)
      exact ((hgSm.pderiv j).continuous).pow 2
    have hW : IsOpen {z : Rd d | ‖z‖ < R ∧ B < c * ∑ i, pderiv g i z ^ 2} :=
      (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const hcont)
    have hW0 : S.toDiffusionTriple.μ {z : Rd d | ‖z‖ < R ∧ B < c * ∑ i, pderiv g i z ^ 2} = 0 := by
      have := ae_iff.1 hae
      refine measure_mono_null (fun z hz => ?_) this
      simp only [Set.mem_ofPred_eq, not_imp, not_le]
      exact hz
    have hnone : ¬ B < c * ∑ j, pderiv g j y ^ 2 := by
      intro hlt
      exact (hW.measure_pos S.toDiffusionTriple.μ ⟨y, hy, hlt⟩).ne' hW0
    rw [not_lt] at hnone
    have hsq : pderiv g i y ^ 2 ≤ m ^ 2 := by
      have h1 : pderiv g i y ^ 2 ≤ ∑ j, pderiv g j y ^ 2 :=
        Finset.single_le_sum (f := fun j => pderiv g j y ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [hmB, le_div_iff₀ hc]; nlinarith
    exact abs_le_of_sq_le_sq' hsq hm0 |> fun h => abs_le.2 h
  have hdiff : ∀ z ∈ Metric.ball (0 : Rd d) R, DifferentiableAt ℝ g z := fun z _ =>
    (hgSm.differentiable (by simp)).differentiableAt
  have hbd : ∀ z ∈ Metric.ball (0 : Rd d) R, ‖fderiv ℝ g z‖ ≤ d * m := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hv : v = ∑ i, v i • (Pi.single i 1 : Rd d) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have e : fderiv ℝ g z v = ∑ i, v i * pderiv g i z := by
      conv_lhs => rw [hv]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]; rfl
    rw [e, Real.norm_eq_abs]
    calc |∑ i, v i * pderiv g i z| ≤ ∑ i, |v i * pderiv g i z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, ‖v‖ * m := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (by simpa using norm_le_pi_norm v i) (hder i z hz) (abs_nonneg _) (norm_nonneg _)
      _ = d * m * ‖v‖ := by simp; ring
  have := (convex_ball (0 : Rd d) R).norm_image_sub_le_of_norm_fderiv_le hdiff hbd
    (by simpa using hy) (by simpa using hx)
  rw [Real.norm_eq_abs] at this
  have e : (d : ℝ) / Real.sqrt (2 * c) * C / Real.sqrt t = d * m := by rw [hm]; ring
  rw [e]
  simpa using this

/-- **U2** (frozen statement): Lipschitz smoothing of `C_c` data, uniformly in the data. -/
theorem rd_smoothing_lip (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d) (hCD : S.CD 0 ∞)
    (hell : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
      c * ∑ i, pderiv g i x ^ 2 ≤ S.toDiffusionTriple.ΓA g g x) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ≥0, 0 < t → ∀ (C : ℝ) (f : C_c(Rd d, ℝ)), (∀ y, |f y| ≤ C) →
      ∀ g : C(Rd d, ℝ), (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[S.toDiffusionTriple.μ] g →
        ∀ x y : Rd d, ‖x‖ < R → ‖y‖ < R → |g x - g y| ≤ K * C / Real.sqrt t * ‖x - y‖ := by
  obtain ⟨K, hK0, hK⟩ := lip_smooth S hA hCD hell R
  refine ⟨K, hK0, fun t ht C f hC g hg x y hx hy => ?_⟩
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hex : ∀ n : ℕ, ∃ h ∈ A₀ d, ∀ z, |h z - f z| < 1 / ((n : ℝ) + 1) := fun n =>
    exists_A₀_approx f (hδ n)
  choose h hhA hhf using hex
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  have hb : ∀ n z, |h n z| ≤ C + δ n := fun n z => by
    have := hhf n z
    have h2 := hC z
    calc |h n z| = |(h n z - f z) + f z| := by ring_nf
      _ ≤ |h n z - f z| + |f z| := abs_add_le _ _
      _ ≤ δ n + C := add_le_add this.le h2
      _ = C + δ n := by ring
  have hclose : ∀ n : ℕ, ∀ z, |g z - S.Pt t ⟨h n, hA₀ ▸ hhA n⟩ z| ≤ δ n := by
    intro n z
    set h' : S.A₀ := ⟨h n, hA₀ ▸ hhA n⟩ with hh'
    have hcl : ∀ᵐ y ∂S.toDiffusionTriple.μ,
        |(S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d → ℝ) y
          - (S.toDiffusionTriple.semigroup t (S.toDiffusionTriple.cls h') : Rd d → ℝ) y| ≤ δ n := by
      refine semigroup_close S t _ _ (hδ n) ?_
      filter_upwards [coeFn_ccL2 (T := S.toDiffusionTriple) f,
        DiffusionTriple.coeFn_cls S.toDiffusionTriple h'] with y a b
      rw [a, b, abs_sub_comm]
      exact (hhf n y).le
    have hae : (fun y => |g y - S.Pt t h' y|) ≤ᵐ[S.toDiffusionTriple.μ] fun _ => δ n := by
      filter_upwards [hcl, hg, S.Pt_ae t h'] with y a b c
      rw [b, c] at a
      exact a
    have hPtc : Continuous (S.Pt t h') := by
      have := S.Pt_mem_A t h'
      rw [hA] at this
      exact (mem_Afull.1 this).continuous
    exact le_of_ae_le_cont S (u := fun y => |g y - S.Pt t h' y|) (v := fun _ => δ n)
      (g.continuous.sub hPtc).abs continuous_const hae z
  have hn : ∀ n : ℕ, |g x - g y| ≤ 2 * δ n + K * (C + δ n) / Real.sqrt t * ‖x - y‖ := by
    intro n
    set h' : S.A₀ := ⟨h n, hA₀ ▸ hhA n⟩ with hh'
    have h1 := hK t ht h' (C + δ n) (hb n) x y hx hy
    have e1 := hclose n x
    have e2 := hclose n y
    calc |g x - g y| = |(g x - S.Pt t h' x) + (S.Pt t h' x - S.Pt t h' y) + (S.Pt t h' y - g y)| := by
          ring_nf
      _ ≤ |g x - S.Pt t h' x| + |S.Pt t h' x - S.Pt t h' y| + |S.Pt t h' y - g y| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ δ n + K * (C + δ n) / Real.sqrt t * ‖x - y‖ + δ n := by
          rw [abs_sub_comm (S.Pt t h' y) (g y)] at *
          have := abs_sub_comm (S.Pt t h' y) (g y)
          linarith
      _ = 2 * δ n + K * (C + δ n) / Real.sqrt t * ‖x - y‖ := by ring
  have h0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => 2 * δ n + K * (C + δ n) / Real.sqrt t * ‖x - y‖) atTop
      (𝓝 (2 * 0 + K * (C + 0) / Real.sqrt t * ‖x - y‖)) :=
    (h0.const_mul 2).add ((((tendsto_const_nhds.add h0).const_mul K).div_const _).mul_const _)
  have := ge_of_tendsto' hlim hn
  simpa using this

end MarkovTriple.Stochastic.R31U
