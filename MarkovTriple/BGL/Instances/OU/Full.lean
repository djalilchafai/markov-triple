import Mathlib
import MarkovTriple.BGL.Instances.OU.Semigroup
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Frozen.Gamma2
import MarkovTriple.BGL.FullBasic

/-!
# The Ornstein–Uhlenbeck triple as a BGL `FullTriple` (D1–D8, S10, S11, F1–F10) and `CD(1,∞)`

`ouStandard : StandardTriple ℝ` and `ouFull : FullTriple ℝ` on `(ℝ, γ = N(0,1))`, `𝒜₀ = C_c^∞(ℝ)`,
`𝒜 = C^∞(ℝ)`, `L f = f'' − x f'`, `Γ(f,g) = f'g'`.  `CD(1,∞)` holds on all of `𝒜`
(`ouFull_CD`, Def. 3.3.14).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

/-- The OU **Standard Markov Triple** (adds S10 ergodicity and S11 conservativeness). -/
noncomputable def ouStandard : StandardTriple ℝ where
  toDiffusionTriple := ouDiff
  ergodic := fun u hu h => ou_ergodic_new u hu h
  conservative := fun _ hu _ t => ou_conservative_new hu t

/-! ### Auxiliary facts used for the extended algebra -/

lemma pos_detect_aux {f : ℝ → ℝ} (hf : Sm f)
    (h : ∀ g ∈ OA₀, 0 ≤ᵐ[γ] g → 0 ≤ ∫ x, g x * f x ∂γ) : ∀ x, 0 ≤ f x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0⟩ := hcon
  have hnhds : ∀ᶠ y in 𝓝 x0, f y < 0 := hf.continuous.continuousAt.eventually_lt
    continuousAt_const hx0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hnhds
  let b : ContDiffBump x0 := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hb_mem : (fun y => b y) ∈ OA₀ := ⟨b.contDiff, b.hasCompactSupport⟩
  have hnn : 0 ≤ᵐ[γ] fun y => b y := Eventually.of_forall fun y => b.nonneg
  have h1 := h _ hb_mem hnn
  have hle : ∀ y, 0 ≤ -(b y * f y) := by
    intro y
    by_cases hy : dist y x0 < r
    · have := hball hy
      have hby : 0 ≤ b y := b.nonneg
      have := mul_nonneg hby (neg_nonneg.2 this.le)
      linarith
    · have : b y = 0 := b.zero_of_le_dist (by simpa [b] using not_lt.1 hy)
      simp [this]
  have hcont : Continuous fun y => -(b y * f y) := (b.continuous.mul hf.continuous).neg
  have hcs : HasCompactSupport fun y => -(b y * f y) :=
    (b.hasCompactSupport.mul_right (f' := f)).neg
  have hne : (fun y => -(b y * f y)) x0 ≠ 0 := by
    have : b x0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp only [this, one_mul, neg_ne_zero]
    exact hx0.ne
  have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := γ) hcs hle hne
  rw [integral_neg] at hpos
  linarith

/-- **The Ornstein–Uhlenbeck Full Markov Triple.** -/
noncomputable def ouFull : FullTriple ℝ where
  toStandardTriple := ouStandard
  A := Afull
  A₀_le := fun f hf => hf.1
  A_measurable := fun f hf => (show Sm f from hf).continuous.measurable
  ideal := fun f hf h hh => ⟨(hh.1).mul (show Sm f from hf), hh.2.mul_right⟩
  pos_detect := fun f hf h =>
    Eventually.of_forall (pos_detect_aux (show Sm f from hf) h)
  A_comp := fun k ψ hψ f hf => sm_comp k ψ hψ f hf
  L_mem_A := fun f hf => sm_Lo (show Sm f from hf)
  ΓA_nonneg := fun f hf => Eventually.of_forall fun x => by
    have := congrFun (ouDiff_ΓA (show Sm f from hf) (show Sm f from hf)) x
    show 0 ≤ ouDiff.ΓA f f x
    rw [this]
    simpa [Go] using mul_self_nonneg (deriv f x)
  diffusion_Γ_A := fun k ψ hψ f hf g hg => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => hf i
    have hg' : Sm g := hg
    have key : ∀ i, ouDiff.ΓA (f i) g = Go (f i) g := fun i => ouDiff_ΓA (hf' i) hg'
    show ouDiff.ΓA (fun x => ψ (fun i => f i x)) g x = _
    rw [ouDiff_ΓA (sm_comp k ψ hψ f hf') hg']
    have := congrFun ((diffusion_s k ψ hψ f hf').1 g hg') x
    refine this.trans ?_
    exact Finset.sum_congr rfl fun i _ => by
      show _ = _ * ouDiff.ΓA (f i) g x
      rw [key i]
  diffusion_L_A := fun k ψ hψ f hf => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => hf i
    have key : ∀ i j, ouDiff.ΓA (f i) (f j) = Go (f i) (f j) :=
      fun i j => ouDiff_ΓA (hf' i) (hf' j)
    have := congrFun ((diffusion_s k ψ hψ f hf').2) x
    refine this.trans ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      show _ = _ * ouDiff.ΓA (f i) (f j) x
      rw [key i j]
  ibp_A := fun f hf g hg => by
    have hf' : Sm f := hf
    have e : ouDiff.ΓA f g = Go f g := ouDiff_ΓA hf' hg.1
    refine ⟨?_, ?_⟩
    · show ∫ x, ouDiff.ΓA f g x ∂γ = -∫ x, g x * Lo f x ∂γ
      rw [e, ibp_cs_left hf' hg, Go_integral_comm]
      simp
    · show ∫ x, ouDiff.ΓA f g x ∂γ = -∫ x, f x * Lo g x ∂γ
      rw [e, ibp_cs_right hf' hg]
      simp [Go]
  semigroup_A := fun t f => by
    rcases eq_zero_or_pos t with h | ht
    · refine ⟨f.1, f.2.1, ?_⟩
      have h0 : ouDiff.semigroup t = 1 := by
        rw [h]; exact (DiffusionTriple.formData ouDiff).semigroup_zero
      show ((ouDiff.semigroup t (ouDiff.cls f) : Lp ℝ 2 γ) : ℝ → ℝ) =ᵐ[γ] f.1
      rw [h0]
      exact DiffusionTriple.coeFn_cls ouDiff f
    · obtain ⟨g, hg, -, -, hae⟩ := Pt_smooth t ht (ouDiff.cls f)
      exact ⟨g, hg, hae⟩
  connected := fun f hf h => by
    have hf' : Sm f := hf
    have h1 : ouDiff.ΓA f f =ᵐ[γ] 0 := h
    rw [ouDiff_ΓA hf' hf'] at h1
    have h2 : deriv f =ᵐ[γ] 0 := by
      filter_upwards [h1] with x hx
      have : deriv f x * deriv f x = 0 := hx
      simpa using this
    have h3 : deriv f = 0 :=
      (Continuous.ae_eq_iff_eq γ hf'.deriv'.continuous continuous_const).1 h2
    have h4 : ∀ x, deriv f x = 0 := fun x => congrFun h3 x
    have h5 := is_const_of_deriv_eq_zero (hf'.differentiable (by simp)) h4
    exact ⟨f 0, Eventually.of_forall fun x => h5 x 0⟩
  esa := fun u hu => ou_esa_core u hu

/-! ### Curvature-dimension condition `CD(1, ∞)` on the whole extended algebra -/

lemma ou_Γ₂_eq {f : ℝ → ℝ} (hf : Sm f) (x : ℝ) :
    ouDiff.Γ₂ f f x = deriv (deriv f) x ^ 2 + deriv f x ^ 2 := by
  have h := ou_Gamma2 hf x
  have e1 : ouDiff.Γ₂ f f x =
      (Lo (Go f f) x - Go f (Lo f) x - Go (Lo f) f x) / 2 := by
    have a := congrFun (ouDiff_ΓA hf hf) ; have b := ouDiff_ΓA hf (sm_Lo hf)
    have c := ouDiff_ΓA (sm_Lo hf) hf
    show (Lo (ouDiff.ΓA f f) x - ouDiff.ΓA f (Lo f) x - ouDiff.ΓA (Lo f) f x) / 2 = _
    rw [ouDiff_ΓA hf hf, b, c]
  rw [e1, ← h]
  have : Go (Lo f) f x = Go f (Lo f) x := by simp [Go, mul_comm]
  rw [this]; ring

/-- **`CD(1,∞)` on all of `𝒜 = C^∞(ℝ)`** (BGL Def. 3.3.14): `Γ₂(f) = f''² + f'² ≥ Γ(f)`. -/
theorem ouFull_CD : ouFull.CD 1 ∞ :=
  ⟨le_top, fun f hf => Eventually.of_forall fun x => by
    have hf' : Sm f := hf
    have e : ouDiff.ΓA f f x = deriv f x ^ 2 := by
      rw [ouDiff_ΓA hf' hf']; simp [Go, sq]
    show 1 * ouDiff.ΓA f f x + ((∞ : ℝ≥0∞)⁻¹).toReal * (Lo f x) ^ 2 ≤ ouDiff.Γ₂ f f x
    rw [e, ou_Γ₂_eq hf']
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, zero_mul, add_zero, one_mul]
    nlinarith [sq_nonneg (deriv (deriv f) x)]⟩

/-- Sanity: `Γ ≠ 0` on the OU triple (witness `f = id`), so it is not the trivial triple. -/
theorem ouFull_Γ_ne_zero : ouDiff.Γ (fun x => x) (fun x => x) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [ouDiff, Go] at this

end MarkovTriple.BGL.Instances.OU

#print axioms MarkovTriple.BGL.Instances.OU.ouDiff
#print axioms MarkovTriple.BGL.Instances.OU.ouStandard
#print axioms MarkovTriple.BGL.Instances.OU.ouFull
#print axioms MarkovTriple.BGL.Instances.OU.ouFull_CD
#print axioms MarkovTriple.BGL.Instances.OU.Pt_mehler
