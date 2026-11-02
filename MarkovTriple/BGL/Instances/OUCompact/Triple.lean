import Mathlib
import MarkovTriple.BGL.Instances.OUCompact.Semigroup
import MarkovTriple.BGL.Instances.OU.Full
import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Frozen.Gamma2

/-!
# The Ornstein–Uhlenbeck triple with `𝒜 = 𝒜₀ = ℬ` as a BGL `CompactTriple`, `CD(1,∞)`

`ouBStandard : StandardTriple ℝ`, `ouBFull : FullTriple ℝ`, `ouBCompact : CompactTriple ℝ` on
`(ℝ, γ = N(0,1))` with `𝒜 = 𝒜₀ = ℬ = {f ∈ C^∞ bounded, f' ∈ 𝒮}`, `L f = f'' − x f'`,
`Γ(f,g) = f'g'`.  `CD(1,∞)` holds on all of `𝒜` (`ouBCompact_CD`), `Γ ≠ 0`.

Note: "compact" is meant in the sense of the frozen surface (`CompactTriple`: `𝒜 = 𝒜₀`, BGL
Def. 3.3.26); the underlying space `ℝ` is not compact.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real SchwartzMap
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OUCompact

/-- Standard Markov Triple (S10, S11). -/
noncomputable def ouBStandard : StandardTriple ℝ where
  toDiffusionTriple := ouB
  ergodic := fun u hu h => ouB_ergodic u hu h
  conservative := fun _ hu _ t => ouB_conservative hu t

/-- **The compact-type Ornstein–Uhlenbeck Full Markov Triple** (`𝒜 = 𝒜₀ = ℬ`). -/
noncomputable def ouBFull : FullTriple ℝ where
  toStandardTriple := ouBStandard
  A := Bfull
  A₀_le := fun f hf => hf
  A_measurable := fun f hf => (show Bm f from hf).sm.continuous.measurable
  ideal := fun f hf h hh => Bm.mul hh hf
  pos_detect := fun f hf h =>
    Eventually.of_forall (MarkovTriple.BGL.Instances.OU.pos_detect_aux (show Bm f from hf).sm
      fun g hg hg0 => h g (bm_of_cs hg.1 hg.2) hg0)
  A_comp := fun k ψ hψ f hf => Bm.comp k ψ hψ f hf
  L_mem_A := fun f hf => bm_Lo hf
  ΓA_nonneg := fun f hf => Eventually.of_forall fun x => by
    have := congrFun (ouB_ΓA (show Bm f from hf).sm (show Bm f from hf).sm) x
    show 0 ≤ ouB.ΓA f f x
    rw [this]
    simpa [Go] using mul_self_nonneg (deriv f x)
  diffusion_Γ_A := fun k ψ hψ f hf g hg => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => (hf i : Bm (f i)).sm
    have hg' : Sm g := (show Bm g from hg).sm
    have key : ∀ i, ouB.ΓA (f i) g = Go (f i) g := fun i => ouB_ΓA (hf' i) hg'
    show ouB.ΓA (fun x => ψ (fun i => f i x)) g x = _
    rw [ouB_ΓA (sm_comp k ψ hψ f hf') hg']
    have := congrFun ((diffusion_s k ψ hψ f hf').1 g hg') x
    refine this.trans ?_
    exact Finset.sum_congr rfl fun i _ => by
      show _ = _ * ouB.ΓA (f i) g x
      rw [key i]
  diffusion_L_A := fun k ψ hψ f hf => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => (hf i : Bm (f i)).sm
    have key : ∀ i j, ouB.ΓA (f i) (f j) = Go (f i) (f j) :=
      fun i j => ouB_ΓA (hf' i) (hf' j)
    have := congrFun ((diffusion_s k ψ hψ f hf').2) x
    refine this.trans ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      show _ = _ * ouB.ΓA (f i) (f j) x
      rw [key i j]
  ibp_A := fun f hf g hg => by
    have hf' : Bm f := hf
    have hg' : Bm g := hg
    have e : ouB.ΓA f g = Go f g := ouB_ΓA hf'.sm hg'.sm
    refine ⟨?_, ?_⟩
    · show ∫ x, ouB.ΓA f g x ∂γ = -∫ x, g x * Lo f x ∂γ
      rw [e, ibp_bm hf' hg', Go_integral_comm']
      simp
    · show ∫ x, ouB.ΓA f g x ∂γ = -∫ x, f x * Lo g x ∂γ
      rw [e, ibp_bm hg' hf']
      simp [Go]
  semigroup_A := fun t f => semigroup_cls_mem t f
  connected := fun f hf h => by
    have hf' : Sm f := (show Bm f from hf).sm
    have h1 : ouB.ΓA f f =ᵐ[γ] 0 := h
    rw [ouB_ΓA hf' hf'] at h1
    have h2 : deriv f =ᵐ[γ] 0 := by
      filter_upwards [h1] with x hx
      have : deriv f x * deriv f x = 0 := hx
      simpa using this
    have h3 : deriv f = 0 :=
      (Continuous.ae_eq_iff_eq γ hf'.deriv'.continuous continuous_const).1 h2
    have h4 : ∀ x, deriv f x = 0 := fun x => congrFun h3 x
    have h5 := is_const_of_deriv_eq_zero (hf'.differentiable (by simp)) h4
    exact ⟨f 0, Eventually.of_forall fun x => h5 x 0⟩
  esa := fun u hu => ouB_esa u hu

/-- **The Ornstein–Uhlenbeck triple as a Compact Markov Triple** (`𝒜 = 𝒜₀`, BGL Def. 3.3.26). -/
noncomputable def ouBCompact : CompactTriple ℝ where
  toFullTriple := ouBFull
  A_eq := fun _ => Iff.rfl

/-! ### Curvature-dimension condition `CD(1,∞)` -/

lemma ouB_Γ₂_eq {f : ℝ → ℝ} (hf : Sm f) (x : ℝ) :
    ouB.Γ₂ f f x = deriv (deriv f) x ^ 2 + deriv f x ^ 2 :=
  MarkovTriple.BGL.Instances.OU.ou_Γ₂_eq hf x

/-- **`CD(1,∞)` on all of `𝒜 = ℬ`** (BGL Def. 3.3.14): `Γ₂(f) = f''² + f'² ≥ Γ(f)`. -/
theorem ouBCompact_CD : ouBCompact.toFullTriple.CD 1 ∞ :=
  ⟨le_top, fun f hf => Eventually.of_forall fun x => by
    have hf' : Sm f := (show Bm f from hf).sm
    have e : ouB.ΓA f f x = deriv f x ^ 2 := by
      rw [ouB_ΓA hf' hf']; simp [Go, sq]
    show 1 * ouB.ΓA f f x + ((∞ : ℝ≥0∞)⁻¹).toReal * (Lo f x) ^ 2 ≤ ouB.Γ₂ f f x
    rw [e, ouB_Γ₂_eq hf']
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, zero_mul, add_zero, one_mul]
    nlinarith [sq_nonneg (deriv (deriv f) x)]⟩

/-- Non-degeneracy: `Γ ≠ 0` (witness `f(x) = x b(x)` with `b` a bump function equal to `1` near `0`,
so `f ∈ C_c^∞ ⊂ ℬ` and `f'(0) = 1`). -/
theorem ouBCompact_Γ_ne_zero : ∃ f ∈ ouBCompact.A₀, ouBCompact.Γ f f ≠ 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hd : HasDerivAt (fun x : ℝ => x * b x) (b 0) 0 := by
    have hbd : Differentiable ℝ b := (b.contDiff (n := 1)).differentiable one_ne_zero
    have := (hasDerivAt_id' (0 : ℝ)).fun_mul (hbd 0).hasDerivAt
    simpa using this
  have hf : (fun x : ℝ => x * b x) ∈ OA₀ :=
    ⟨contDiff_id.mul b.contDiff, b.hasCompactSupport.mul_left⟩
  refine ⟨fun x => x * b x, (bm_of_cs hf.1 hf.2 : _ ∈ ouB.A₀), ?_⟩
  intro h
  have := congrFun h 0
  have e : deriv (fun x : ℝ => x * b x) 0 = 1 := by rw [hd.deriv, hb]
  simp [ouBCompact, ouBFull, ouBStandard, ouB, Go, e] at this

end MarkovTriple.BGL.Instances.OUCompact
