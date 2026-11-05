import Mathlib
import MarkovTriple.Stochastic.R30T.Continuity
import MarkovTriple.BGL.Theory.Interp.JensenGrad

/-!
# Round 30 (T), part 3: locally uniform Lipschitz bound for `P_t h`, `h ∈ C_c^∞`, under `CD(0,∞)` + local ellipticity

BGL Cor. 3.3.19 (`Γ(P_t h) ≤ P_t Γ(h)`, here `FullTriple.gradient_bound_unconditional` with `ρ = 0`) + `P_t Γ(h) ≤ ‖Γ h‖_∞` (sub-Markov)
+ local ellipticity `hell` turn the a.e. gradient bound into `|∇ P_t h| ≤ M` everywhere on balls (continuity + full support),
hence a Lipschitz bound on balls, uniform in `t`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R30T

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24

variable {d : ℕ} (S : FullTriple (Rd d)) [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ]
  [S.toDiffusionTriple.μ.IsOpenPosMeasure]

/-- `|x| ≤ N` from `x² ≤ N` is not what we need: crude bound `|x| ≤ (x² + 1)/2`. -/
lemma abs_le_half_sq_add (x : ℝ) : |x| ≤ (x ^ 2 + 1) / 2 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

omit [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ] in
/-- **Local Lipschitz bound, uniform in `t`**. -/
theorem lip_bound (hA : S.A = Afull d) (hCD : S.CD 0 ∞)
    (hell : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
      c * ∑ i, pderiv g i x ^ 2 ≤ S.toDiffusionTriple.ΓA g g x)
    (h : S.A₀) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ≥0) (x y : Rd d), ‖x‖ < R → ‖y‖ < R →
      |S.Pt t h x - S.Pt t h y| ≤ K * ‖x - y‖ := by
  obtain ⟨c, hc, hcell⟩ := hell R
  set γ : S.A₀ := ⟨S.toDiffusionTriple.ΓA h.1 h.1, S.ΓA_self_mem_A₀ h.2⟩ with hγ
  obtain ⟨C, hC⟩ := S.toDiffusionTriple.bounded γ.1 γ.2
  set B : ℝ := |C| + 1 with hB
  have hBpos : 0 < B := by positivity
  have hγB : ∀ x, γ.1 x ≤ B := fun x => (le_abs_self _).trans ((hC x).trans (by rw [hB]; linarith [le_abs_self C]))
  -- sub-Markov bound on `P_t Γ(h)`
  have hPγ : ∀ t : ℝ≥0, (S.toDiffusionTriple.semigroup t (S.toDiffusionTriple.cls γ) : Rd d → ℝ) ≤ᵐ[S.toDiffusionTriple.μ] fun _ => B := by
    intro t
    refine semigroup_le_const (T := S.toDiffusionTriple) t _ hBpos ?_
    filter_upwards [DiffusionTriple.coeFn_cls S.toDiffusionTriple γ] with x hx
    rw [hx]; exact hγB x
  set M : ℝ := B / c + 1 with hM
  have hMpos : 0 ≤ M := by positivity
  have hder : ∀ (t : ℝ≥0) (i : Fin d) (y : Rd d), ‖y‖ < R → |pderiv (S.Pt t h) i y| ≤ M := by
    intro t i y hy
    set g := S.Pt t h with hg
    have hgSm : Sm g := by
      have := S.Pt_mem_A t h
      rw [hA] at this
      exact mem_Afull.1 this
    have hGB := S.gradient_bound_unconditional hCD (le_refl 0) h t
    -- a.e. bound on the ball
    have hae : ∀ᵐ z ∂S.toDiffusionTriple.μ, ‖z‖ < R → c * ∑ i, pderiv g i z ^ 2 ≤ B := by
      filter_upwards [hGB, hPγ t] with z h1 h2 hz
      have h3 := hcell g hgSm z hz.le
      simp only [mul_zero, zero_mul, Real.exp_zero, one_mul] at h1
      exact h3.trans (h1.trans h2)
    -- continuity of the left side
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
    have hsq : pderiv g i y ^ 2 ≤ B / c := by
      have h1 : pderiv g i y ^ 2 ≤ ∑ j, pderiv g j y ^ 2 :=
        Finset.single_le_sum (f := fun j => pderiv g j y ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [le_div_iff₀ hc]; nlinarith
    calc |pderiv g i y| ≤ (pderiv g i y ^ 2 + 1) / 2 := abs_le_half_sq_add _
      _ ≤ M := by rw [hM]; have : (0:ℝ) ≤ B / c := by positivity
                  linarith
  refine ⟨d * M, by positivity, fun t x y hx hy => ?_⟩
  set g := S.Pt t h with hg
  have hgSm : Sm g := by
    have := S.Pt_mem_A t h
    rw [hA] at this
    exact mem_Afull.1 this
  have hdiff : ∀ z ∈ Metric.ball (0 : Rd d) R, DifferentiableAt ℝ g z := fun z _ =>
    (hgSm.differentiable (by simp)).differentiableAt
  have hbd : ∀ z ∈ Metric.ball (0 : Rd d) R, ‖fderiv ℝ g z‖ ≤ d * M := by
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
      _ ≤ ∑ _i : Fin d, ‖v‖ * M := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (by simpa using norm_le_pi_norm v i) (hder t i z hz) (abs_nonneg _) (norm_nonneg _)
      _ = d * M * ‖v‖ := by simp; ring
  have := (convex_ball (0 : Rd d) R).norm_image_sub_le_of_norm_fderiv_le hdiff hbd
    (by simpa using hy) (by simpa using hx)
  rw [Real.norm_eq_abs] at this
  simpa using this

end MarkovTriple.Stochastic.R30T
