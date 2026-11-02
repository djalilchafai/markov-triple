import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple
import MarkovTriple.BGL.Frozen.GammaA
import MarkovTriple.BGL.Analysis.OU.Stable

/-!
# The Ornstein–Uhlenbeck triple as a BGL `DiffusionTriple` (D1–D8)

`E = ℝ`, `μ = γ = gaussianReal 0 1`, `𝒜₀ = C_c^∞(ℝ)`, `L f = f'' − x f'`, `Γ(f,g) = f' g'`.
Reuses the pointwise calculus of the old OU files (`MarkovTriple.Sanity.OU`).  New here: boundedness
of test functions, the (monotone) exhaustion sequence `u_n(x) = s(2 − (x/(n+1))²)` with
`s = Real.smoothTransition`, D8 (`∫ L f = 0`), `finite_prob`, and the a.e. diffusion property in the
BGL shape.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

/-- `C_c^∞(ℝ)` (the old OU algebra). -/
local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

/-- `γ` charges every nonempty open set. -/
instance : γ.IsOpenPosMeasure :=
  ⟨fun _U hU hne h0 => hU.measure_ne_zero volume hne
    ((ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero) h0)⟩

/-! ### The exhaustion sequence -/

/-- `u_n(x) = s(2 − (x/(n+1))²)`: smooth, `=1` for `|x| ≤ n+1`, `=0` for `|x| ≥ 2(n+1)`. -/
noncomputable def expo (n : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (2 - (x / ((n : ℝ) + 1)) ^ 2)

lemma expo_sm (n : ℕ) : Sm (expo n) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_id.div_const _).pow 2))

lemma expo_cs (n : ℕ) : HasCompactSupport (expo n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * ((n : ℝ) + 1))) fun x hx => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx' : 2 * ((n : ℝ) + 1) < |x| := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hx
  unfold expo
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 2 < |x / ((n : ℝ) + 1)| := by
    rw [abs_div, abs_of_pos hn, lt_div_iff₀ hn]; linarith
  have : 4 < (x / ((n : ℝ) + 1)) ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_nonneg (x / ((n : ℝ) + 1))]) h1
    rw [sq_abs] at this
    nlinarith
  linarith

lemma expo_mono (x : ℝ) : Monotone fun n : ℕ => expo n x := by
  intro m n hmn
  unfold expo
  apply Real.smoothTransition.monotone
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
  have h1 : |x / ((n : ℝ) + 1)| ≤ |x / ((m : ℝ) + 1)| := by
    rw [abs_div, abs_div, abs_of_pos hm, abs_of_pos (hm.trans_le hmn')]
    exact div_le_div_of_nonneg_left (abs_nonneg x) hm hmn'
  have := sq_le_sq' (by linarith [abs_nonneg (x / ((n : ℝ) + 1))]) h1
  rw [sq_abs, sq_abs] at this
  linarith

lemma expo_tendsto (x : ℝ) : Tendsto (fun n => expo n x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  symm
  unfold expo
  apply Real.smoothTransition.one_of_one_le
  have hn' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : |x / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_div, abs_of_pos hn', div_le_one hn']
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have : (x / ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
    have := sq_le_one_iff_abs_le_one (x / ((n : ℝ) + 1)) |>.2 h1
    exact this
  linarith

/-! ### Basic facts on `𝒜₀` -/

lemma A₀_bounded {f : ℝ → ℝ} (hf : f ∈ OA₀) : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  exact ⟨C, fun x => by simpa using hC x⟩

lemma integral_Lo_zero {f : ℝ → ℝ} (hf : f ∈ OA₀) : ∫ x, Lo f x ∂γ = 0 := by
  have := ibp_cs_right (f := fun _ : ℝ => (1 : ℝ)) (g := f) contDiff_const hf
  simpa using this

lemma Go_integral_comm (f g : ℝ → ℝ) : ∫ x, deriv g x * deriv f x ∂γ = ∫ x, Go f g x ∂γ :=
  integral_congr_ae (ae_of_all _ fun x => by simp [Go, mul_comm])

/-- **The Ornstein–Uhlenbeck Diffusion Markov Triple** (D1–D8). -/
noncomputable def ouDiff : DiffusionTriple ℝ where
  μ := γ
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := OA₀
  measurable := fun f hf => hf.1.continuous.measurable
  bounded := fun f hf => A₀_bounded hf
  memLp := fun f hf p _ _ => memLp_A₀ hf p
  dense := fun p hp hp' => by
    have := hp
    exact dense_Lp p hp'
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_A₀ k ψ hψ h0 f hf
  exhaustion := ⟨expo, fun n => ⟨expo_sm n, expo_cs n⟩,
    fun n => Eventually.of_forall fun x => expo_mono x (Nat.le_succ n),
    Eventually.of_forall expo_tendsto⟩
  Γ := Go
  L := Lo
  Γ_mem := fun f hf g hg => A₀.Go_mem hf hg
  L_mem := fun f hf => A₀.Lo_mem hf
  Γ_symm := fun f _ g _ => Eventually.of_forall fun x => by simp [Go, mul_comm]
  Γ_add := fun f hf f' hf' g _ => Eventually.of_forall fun x => by
    simp [Go, deriv_add_s hf.1 hf'.1, add_mul]
  Γ_smul := fun c f hf g _ => Eventually.of_forall fun x => by
    simp [Go, deriv_smul_s c hf.1, mul_assoc]
  Γ_nonneg := fun f _ => Eventually.of_forall fun x => by
    simpa [Go] using mul_self_nonneg (deriv f x)
  diffusion := fun k ψ hψ _ f hf g hg => Eventually.of_forall fun x =>
    congrFun ((diffusion_s k ψ hψ f (fun i => (hf i).1)).1 g hg.1) x
  ibp := fun f hf g hg => by
    have := ibp_cs_left hf.1 hg
    rw [this, Go_integral_comm]
  integral_L := fun f hf => integral_Lo_zero hf

/-- On smooth functions the formula-defined `ΓA` of the OU triple is `f' g'`. -/
lemma ouDiff_ΓA {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) : ouDiff.ΓA f g = Go f g := by
  funext x
  have e : ouDiff.ΓA f g x = (Lo (f * g) x - f x * Lo g x - g x * Lo f x) / 2 := rfl
  rw [e, Lo_mul hf hg x]; simp only [Go]; ring

end MarkovTriple.BGL.Instances.OU
