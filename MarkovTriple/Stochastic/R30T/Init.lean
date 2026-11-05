import Mathlib
import MarkovTriple.Stochastic.R30T.Lip

/-!
# Round 30 (T), part 4: pointwise initial condition `P_t f (x) → f(x)` (G3)

Step A (`f ∈ C_c^∞`): equi-Lipschitz (`lip_bound`) + `P_t f → f` in `L²` (strong continuity) ⇒ pointwise convergence at every `x`
(Chebyshev on a small ball).  Step B (`f ∈ C_c`): uniform approximation by `C_c^∞` and the sub-Markov bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R30T

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24

variable {d : ℕ} (S : FullTriple (Rd d)) [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ]
  [S.toDiffusionTriple.μ.IsOpenPosMeasure]

/-- Chebyshev: if `‖w‖² < η² μ(B)` then some point of `B` has `|w| < η`. -/
lemma exists_small_of_norm_lt {μ : Measure (Rd d)} {B : Set (Rd d)} {η : ℝ} (hη : 0 < η) (w : Lp ℝ 2 μ) (w' : Rd d → ℝ) (hw' : (w : Rd d → ℝ) =ᵐ[μ] w')
    (hw : ‖w‖ ^ 2 < η ^ 2 * μ.real B) :
    ∃ y ∈ B, |w' y| < η := by
  by_contra hcon
  push Not at hcon
  have hint : Integrable (fun y => (w : Rd d → ℝ) y ^ 2) μ := (Lp.memLp w).integrable_sq
  have hnorm : ‖w‖ ^ 2 = ∫ y, (w : Rd d → ℝ) y ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    simp [sq]
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun y => (w : Rd d → ℝ) y ^ 2)
    (Eventually.of_forall fun y => sq_nonneg _) hint (η ^ 2)
  have hfin : μ {y | η ^ 2 ≤ (w : Rd d → ℝ) y ^ 2} ≠ ∞ := by
    have := hint.measure_ge_lt_top (ε := η ^ 2) (by positivity)
    refine ne_of_lt (lt_of_le_of_lt (measure_mono fun y hy => ?_) this)
    have hy' : η ^ 2 ≤ (w : Rd d → ℝ) y ^ 2 := hy
    simpa using hy'
  have hsub : B ≤ᵐ[μ] {y | η ^ 2 ≤ (w : Rd d → ℝ) y ^ 2} := by
    filter_upwards [hw'] with y hyw hy
    have := hcon y hy
    rw [← hyw] at this
    show η ^ 2 ≤ _
    nlinarith [sq_abs ((w : Rd d → ℝ) y), abs_nonneg ((w : Rd d → ℝ) y)]
  have hmono : μ.real B ≤ μ.real {y | η ^ 2 ≤ (w : Rd d → ℝ) y ^ 2} :=
    ENNReal.toReal_mono hfin (measure_mono_ae hsub)
  have : η ^ 2 * μ.real B ≤ ‖w‖ ^ 2 := by
    rw [hnorm]
    exact (mul_le_mul_of_nonneg_left hmono (by positivity)).trans hmark
  linarith

/-- **Step A**: pointwise initial condition for `h ∈ C_c^∞`. -/
theorem init_A₀ (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d) (hCD : S.CD 0 ∞)
    (hell : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
      c * ∑ i, pderiv g i x ^ 2 ≤ S.toDiffusionTriple.ΓA g g x)
    (h : Rd d → ℝ) (hh : h ∈ A₀ d) (x : Rd d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ → |S.Pt t ⟨h, hA₀ ▸ hh⟩ x - h x| < ε := by
  set h' : S.A₀ := ⟨h, hA₀ ▸ hh⟩ with hh'
  obtain ⟨K, hK0, hK⟩ := lip_bound S hA hCD hell h' (‖x‖ + 2)
  have hcont : Continuous h := (mem_A₀.1 hh).1.continuous
  obtain ⟨r1, hr1, hr1h⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := x)) (ε / 3) (by positivity)
  set r : ℝ := min (min r1 1) (ε / (3 * (K + 1))) with hr
  have hr0 : 0 < r := lt_min (lt_min hr1 one_pos) (by positivity)
  have hrr1 : r ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
  have hrr2 : r ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hKr : K * r < ε / 3 := by
    have h1 : r ≤ ε / (3 * (K + 1)) := min_le_right _ _
    calc K * r ≤ K * (ε / (3 * (K + 1))) := mul_le_mul_of_nonneg_left h1 hK0
      _ < ε / 3 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  set μ := S.toDiffusionTriple.μ with hμ
  set B : Set (Rd d) := Metric.ball x r with hB
  have hBpos : 0 < μ.real B := by
    have h1 : 0 < μ B := Metric.isOpen_ball.measure_pos μ ⟨x, Metric.mem_ball_self hr0⟩
    exact ENNReal.toReal_pos h1.ne' (measure_ball_lt_top).ne
  set η : ℝ := ε / 3 with hη
  have hη0 : 0 < η := by positivity
  set ρ0 : ℝ := η * Real.sqrt (μ.real B) with hρ0
  have hρ0pos : 0 < ρ0 := by positivity
  set u : Lp ℝ 2 μ := S.toDiffusionTriple.cls h' with hu
  have hcs : ContinuousAt (fun t : ℝ≥0 => S.toDiffusionTriple.semigroup t u) 0 :=
    (DiffusionTriple.continuous_semigroup_apply S.toDiffusionTriple u).continuousAt
  obtain ⟨δ0, hδ0, hδ⟩ := Metric.continuousAt_iff.1 hcs ρ0 hρ0pos
  refine ⟨δ0.toNNReal, by simpa using hδ0, fun t ht => ?_⟩
  have htδ : dist t 0 < δ0 := by
    rw [NNReal.dist_eq]
    have : (t : ℝ) < δ0 := by
      have := NNReal.coe_lt_coe.2 ht
      simpa [Real.coe_toNNReal _ hδ0.le] using this
    simpa using this
  have hd := hδ htδ
  rw [DiffusionTriple.semigroup_zero] at hd
  simp only [one_apply_eq_self] at hd
  set w : Lp ℝ 2 μ := S.toDiffusionTriple.semigroup t u - u with hw
  have hwn : ‖w‖ ^ 2 < η ^ 2 * μ.real B := by
    have : ‖w‖ < ρ0 := by rwa [dist_eq_norm] at hd
    calc ‖w‖ ^ 2 < ρ0 ^ 2 := by gcongr
      _ = η ^ 2 * μ.real B := by
        rw [hρ0, mul_pow, Real.sq_sqrt hBpos.le]
  have hwae : (w : Rd d → ℝ) =ᵐ[μ] fun y => S.Pt t h' y - h y := by
    filter_upwards [Lp.coeFn_sub (S.toDiffusionTriple.semigroup t u) u, S.Pt_ae t h',
      DiffusionTriple.coeFn_cls S.toDiffusionTriple h'] with y a b c
    rw [hw, a]; simp only [Pi.sub_apply]
    rw [hu, b, c]
  obtain ⟨y, hyB, hy⟩ := exists_small_of_norm_lt hη0 w _ hwae hwn
  have hyB' : dist y x < r := hyB
  have hxy : ‖x - y‖ < r := by rw [← dist_eq_norm, dist_comm]; exact hyB'
  have hlip := hK t x y (by linarith) (by
    have := norm_sub_norm_le y x
    rw [dist_eq_norm] at hyB'
    linarith)
  have hhy : |h y - h x| < ε / 3 := by
    have := hr1h (show dist y x < r1 from lt_of_lt_of_le hyB' hrr1)
    rwa [Real.dist_eq] at this
  calc |S.Pt t h' x - h x| = |(S.Pt t h' x - S.Pt t h' y) + (S.Pt t h' y - h y) + (h y - h x)| := by ring_nf
    _ ≤ |S.Pt t h' x - S.Pt t h' y| + |S.Pt t h' y - h y| + |h y - h x| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < ε := by
        have h1 : |S.Pt t h' x - S.Pt t h' y| ≤ K * r :=
          hlip.trans (mul_le_mul_of_nonneg_left hxy.le hK0)
        have h2 : |S.Pt t h' y - h y| < ε / 3 := hy
        linarith

omit [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ] [S.toDiffusionTriple.μ.IsOpenPosMeasure] in
/-- `L^∞`-contractivity of `P_t` (sub-Markov) in the form: `|u - v| ≤ c` a.e. implies `|P_t u - P_t v| ≤ c` a.e. -/
lemma semigroup_close (t : ℝ≥0) (u v : Lp ℝ 2 S.toDiffusionTriple.μ) {c : ℝ} (hc : 0 < c)
    (h : ∀ᵐ y ∂S.toDiffusionTriple.μ, |(u : Rd d → ℝ) y - (v : Rd d → ℝ) y| ≤ c) :
    ∀ᵐ y ∂S.toDiffusionTriple.μ, |(S.toDiffusionTriple.semigroup t u : Rd d → ℝ) y
      - (S.toDiffusionTriple.semigroup t v : Rd d → ℝ) y| ≤ c := by
  have h1 : ((u - v : Lp ℝ 2 S.toDiffusionTriple.μ) : Rd d → ℝ) ≤ᵐ[S.toDiffusionTriple.μ] fun _ => c := by
    filter_upwards [Lp.coeFn_sub u v, h] with y a b
    rw [a]; exact (le_abs_self _).trans b
  have h2 : ((v - u : Lp ℝ 2 S.toDiffusionTriple.μ) : Rd d → ℝ) ≤ᵐ[S.toDiffusionTriple.μ] fun _ => c := by
    filter_upwards [Lp.coeFn_sub v u, h] with y a b
    rw [a]; simp only [Pi.sub_apply]
    rw [abs_sub_comm] at b; exact (le_abs_self _).trans b
  have s1 := semigroup_le_const (T := S.toDiffusionTriple) t _ hc h1
  have s2 := semigroup_le_const (T := S.toDiffusionTriple) t _ hc h2
  rw [(S.toDiffusionTriple.semigroup t).map_sub] at s1 s2
  filter_upwards [s1, s2, Lp.coeFn_sub (S.toDiffusionTriple.semigroup t u) (S.toDiffusionTriple.semigroup t v),
    Lp.coeFn_sub (S.toDiffusionTriple.semigroup t v) (S.toDiffusionTriple.semigroup t u)] with y a b c1 d1
  simp only [Pi.sub_apply] at a b c1 d1
  rw [c1] at a; rw [d1] at b
  rw [abs_le]; constructor <;> linarith

/-- **G3** (frozen statement): pointwise initial condition for `f ∈ C_c`. -/
theorem rd_initial_condition (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d) (hCD : S.CD 0 ∞)
    (hell : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
      c * ∑ i, pderiv g i x ^ 2 ≤ S.toDiffusionTriple.ΓA g g x)
    (f : C_c(Rd d, ℝ)) (x : Rd d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ → ∀ g : C(Rd d, ℝ),
      (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[S.toDiffusionTriple.μ] g → |g x - f x| < ε := by
  obtain ⟨h, hhA, hhf⟩ := exists_A₀_approx f (show 0 < ε / 3 by positivity)
  obtain ⟨δ, hδ, hδt⟩ := init_A₀ S hA hA₀ hCD hell h hhA x (show 0 < ε / 3 by positivity)
  refine ⟨δ, hδ, fun t ht g hg => ?_⟩
  set h' : S.A₀ := ⟨h, hA₀ ▸ hhA⟩ with hh'
  have hcl : ∀ᵐ y ∂S.toDiffusionTriple.μ,
      |(S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d → ℝ) y
        - (S.toDiffusionTriple.semigroup t (S.toDiffusionTriple.cls h') : Rd d → ℝ) y| ≤ ε / 3 := by
    refine semigroup_close S t _ _ (by positivity) ?_
    filter_upwards [coeFn_ccL2 (T := S.toDiffusionTriple) f, DiffusionTriple.coeFn_cls S.toDiffusionTriple h']
      with y a b
    rw [a, b, abs_sub_comm]
    exact (hhf y).le
  have hae : (fun y => |g y - S.Pt t h' y|) ≤ᵐ[S.toDiffusionTriple.μ] fun _ => ε / 3 := by
    filter_upwards [hcl, hg, S.Pt_ae t h'] with y a b c
    rw [b, c] at a
    exact a
  have hPtc : Continuous (S.Pt t h') := by
    have := S.Pt_mem_A t h'
    rw [hA] at this
    exact (mem_Afull.1 this).continuous
  have hev := le_of_ae_le_cont S (u := fun y => |g y - S.Pt t h' y|) (v := fun _ => ε / 3)
    (g.continuous.sub hPtc).abs continuous_const hae x
  have hA1 := hδt t ht
  have hf1 := hhf x
  calc |g x - f x| = |(g x - S.Pt t h' x) + (S.Pt t h' x - h x) + (h x - f x)| := by ring_nf
    _ ≤ |g x - S.Pt t h' x| + |S.Pt t h' x - h x| + |h x - f x| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < ε := by linarith

end MarkovTriple.Stochastic.R30T
