import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Basic
import MarkovTriple.BGL.Instances.Lebesgue.Diffusion
import MarkovTriple.BGL.Frozen.CD

/-!
# The zonal Gegenbauer triple (`λ = 3/2`) on `(-1,1)` with `𝒜₀ = C_c^∞((-1,1))` as a `DiffusionTriple` (S1)

`L f = (1-x²) f'' - 4 x f'`, `Γ(f,g) = (1-x²) f' g'`, `μ = (3/4)(1-x²) dx`.
Key identity: `(1-x²) L f = ((1-x²)² f')'`.  See `STATEMENTS_R22_E2.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open MarkovTriple.BGL.Instances.Interval

/-- `L f = (1-x²) f'' - 4 x f'`. -/
noncomputable def goL (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1 - x ^ 2) * deriv (deriv f) x - 4 * x * deriv f x

/-- `Γ(f,g) = (1-x²) f' g'`. -/
noncomputable def goΓ (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1 - x ^ 2) * (deriv f x * deriv g x)

/-- a statement true for all `x ∈ (-1,1)` holds `goμ`-a.e. -/
lemma ae_go {p : ℝ → Prop} (h : ∀ x ∈ Ioo (-1 : ℝ) 1, p x) : ∀ᵐ x ∂goμ, p x :=
  Measure.absolutelyContinuous_of_le goμ_le
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall h))

lemma sm_w1 : Lebesgue.Sm (fun x : ℝ => 1 - x ^ 2) := contDiff_const.sub (contDiff_id.pow 2)

lemma sm_w2 : Lebesgue.Sm (fun x : ℝ => (1 - x ^ 2) ^ 2) := sm_w1.pow 2

lemma sm_w4 : Lebesgue.Sm (fun x : ℝ => 4 * x) := contDiff_const.mul contDiff_id

lemma goL_mem {f : ℝ → ℝ} (hf : f ∈ goA₀) : goL f ∈ goA₀ := by
  have h1 := smul_mem_goA₀ (p := fun x : ℝ => 1 - x ^ 2) sm_w1
    (deriv_mem_goA₀ (deriv_mem_goA₀ hf))
  have h2 := smul_mem_goA₀ (p := fun x : ℝ => 4 * x) sm_w4 (deriv_mem_goA₀ hf)
  have := sub_mem h1 h2
  convert this using 1
  funext x
  simp only [goL, Pi.sub_apply, mul_assoc]

lemma goΓ_mem {f g : ℝ → ℝ} (hf : f ∈ goA₀) (hg : g ∈ goA₀) : goΓ f g ∈ goA₀ :=
  smul_mem_goA₀ (p := fun x : ℝ => 1 - x ^ 2) sm_w1
    (mul_mem (deriv_mem_goA₀ hf) (deriv_mem_goA₀ hg))

/-- `P_f = (1-x²)² f'`. -/
lemma goP_mem {f : ℝ → ℝ} (hf : f ∈ goA₀) : (fun x => (1 - x ^ 2) ^ 2 * deriv f x) ∈ goA₀ :=
  smul_mem_goA₀ (p := fun x : ℝ => (1 - x ^ 2) ^ 2) sm_w2 (deriv_mem_goA₀ hf)

/-- `((1-x²)² f')' = (1-x²) L f`. -/
lemma deriv_goP {f : ℝ → ℝ} (hf : Lebesgue.Sm f) (x : ℝ) :
    deriv (fun x => (1 - x ^ 2) ^ 2 * deriv f x) x = (1 - x ^ 2) * goL f x := by
  have h1 : HasDerivAt (fun x : ℝ => (1 - x ^ 2) ^ 2) (2 * (1 - x ^ 2) * (-(2 * x))) x := by
    have := (((hasDerivAt_pow 2 x).const_sub 1).pow 2)
    convert this using 1
    simp
  have h2 := h1.mul (hf.deriv'.hasDerivAt x)
  refine (h2.deriv : deriv (fun x => (1 - x ^ 2) ^ 2 * deriv f x) x = _).trans ?_
  simp only [goL]
  ring

lemma integral_go_L {f g : ℝ → ℝ} (hf : Lebesgue.Sm f) (hg : g ∈ goA₀) :
    ∫ x, g x * goL f x ∂goμ = -∫ x, goΓ f g x ∂goμ := by
  have hv : Lebesgue.Sm (fun x => (1 - x ^ 2) ^ 2 * deriv f x) :=
    ((contDiff_const.sub (contDiff_id.pow 2)).pow 2).mul hf.deriv'
  have h := Lebesgue.ibp_cs (goA₀_smooth hg) hv (Or.inl (goA₀_cs hg))
  rw [integral_goμ (fun x hx => by simp [zero_off_go hg hx]),
    integral_goμ (fun x hx => by simp [goΓ, zero_off_go (deriv_mem_goA₀ hg) hx])]
  have e1 : ∫ x, (3 / 4 * (1 - x ^ 2)) * (g x * goL f x) = 3 / 4 * ∫ x, g x * deriv
      (fun x => (1 - x ^ 2) ^ 2 * deriv f x) x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [deriv_goP hf]; ring
  have e2 : ∫ x, (3 / 4 * (1 - x ^ 2)) * goΓ f g x = 3 / 4 * ∫ x, deriv g x *
      ((1 - x ^ 2) ^ 2 * deriv f x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [goΓ]; ring
  rw [e1, e2, h]; ring

lemma integral_go_L_self {f : ℝ → ℝ} (hf : f ∈ goA₀) : ∫ x, goL f x ∂goμ = 0 := by
  have hv : Lebesgue.Sm (fun x => (1 - x ^ 2) ^ 2 * deriv f x) :=
    ((contDiff_const.sub (contDiff_id.pow 2)).pow 2).mul (goA₀_smooth hf).deriv'
  have hcs : HasCompactSupport (fun x => (1 - x ^ 2) ^ 2 * deriv f x) :=
    goA₀_cs (goP_mem hf)
  have h := Lebesgue.ibp_cs (u := fun _ => (1 : ℝ)) contDiff_const hv (Or.inr hcs)
  rw [integral_goμ (fun x hx => by simp [goL, zero_off_go (deriv_mem_goA₀ hf) hx,
    zero_off_go (deriv_mem_goA₀ (deriv_mem_goA₀ hf)) hx])]
  have e1 : ∫ x, (3 / 4 * (1 - x ^ 2)) * goL f x = 3 / 4 * ∫ x, 1 * deriv
      (fun x => (1 - x ^ 2) ^ 2 * deriv f x) x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [deriv_goP (goA₀_smooth hf)]; ring
  rw [e1, h]; simp

/-- **The zonal Gegenbauer triple (`λ = 3/2`) on `(-1,1)`** (S1): `𝒜₀ = C_c^∞((-1,1))`. -/
@[reducible] noncomputable def goDiff : MarkovTriple.BGL.DiffusionTriple ℝ where
  μ := goμ
  sigmaFinite := inferInstance
  finite_prob := fun _ => isProb_goμ
  A₀ := goA₀
  measurable := fun f hf => (goA₀_smooth hf).continuous.measurable
  bounded := fun f hf => by
    obtain ⟨C, hC⟩ := (goA₀_smooth hf).continuous.bounded_above_of_compact_support (goA₀_cs hf)
    exact ⟨C, fun x => by simpa using hC x⟩
  memLp := fun f hf p _ _ => (Lebesgue.memLp_of (goA₀_le hf) p).mono_measure goμ_le_volume
  dense := fun p hp hp' => by
    have := hp
    exact goA₀_dense p hp'
  comp_mem := fun k ψ hψ h0 f hf => comp_mem_goA₀ k ψ hψ h0 f hf
  exhaustion := ⟨gocut, gocut_mem, fun n => Filter.Eventually.of_forall fun x => gocut_mono n x,
    ae_go fun _ hx => gocut_tendsto hx⟩
  Γ := goΓ
  L := goL
  Γ_mem := fun f hf g hg => goΓ_mem hf hg
  L_mem := fun f hf => goL_mem hf
  Γ_symm := fun f _ g _ => Filter.Eventually.of_forall fun x => by simp [goΓ, mul_comm]
  Γ_add := fun f hf f' hf' g _ => Filter.Eventually.of_forall fun x => by
    simp [goΓ, Lebesgue.deriv_add_sm hf.1 hf'.1]; ring
  Γ_smul := fun c f hf g _ => Filter.Eventually.of_forall fun x => by
    simp [goΓ, Lebesgue.deriv_smul_sm c hf.1]; ring
  Γ_nonneg := fun f _ => ae_go fun x hx => by
    simp only [Pi.zero_apply, goΓ]
    exact mul_nonneg (by nlinarith [hx.1, hx.2]) (mul_self_nonneg _)
  diffusion := fun k ψ hψ _ f hf g _ =>
    Filter.Eventually.of_forall fun x => by
      have := congrFun ((Lebesgue.diffusion_c k ψ hψ f (fun i => (hf i).1)).1 g) x
      simp only [goΓ]
      rw [show deriv (fun x => ψ fun i => f i x) x * deriv g x =
        Lebesgue.Gf (fun x => ψ fun i => f i x) g x from rfl, this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Lebesgue.Gf]; ring
  ibp := fun f hf g hg => integral_go_L hf.1 hg
  integral_L := fun f hf => integral_go_L_self hf

end MarkovTriple.BGL.Instances.GegenbauerOpen
