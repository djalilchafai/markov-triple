import MarkovTriple.Sanity.OU.Stable
import MarkovTriple.Frozen.CDFull
import MarkovTriple.FunctionalInequalities.Poincare

/-! # OU (Part 15): the `FullMarkovTriple`, `CD(1,∞)` on `𝒜`, ergodicity, Gaussian Poincaré -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

lemma Go_comm_integral {f g : ℝ → ℝ} : ∫ x, deriv g x * deriv f x ∂γ = ∫ x, Go f g x ∂γ :=
  integral_congr_ae (ae_of_all _ fun x => by simp [Go, mul_comm])

/-- **The Ornstein–Uhlenbeck full Markov triple** on `(ℝ, γ)`:
`𝒜₀ = C_c^∞(ℝ)`, `𝒜 = C^∞(ℝ)`, `L f = f'' − x f'`, `Γ(f,g) = f' g'`. -/
noncomputable def ouFull : FullMarkovTriple ℝ where
  toMarkovTriple := ouTriple
  A := Afull
  A₀_le := fun f hf => A₀.le hf
  A_measurable := fun f hf => (show Sm f from hf).continuous.measurable
  A_comp := fun k ψ hψ f hf => sm_comp k ψ hψ f hf
  L_mem_A := fun f hf => sm_Lo hf
  Γ_mem_A := fun f hf g hg => sm_Go hf hg
  Γ_symm_A := fun f _ g _ => by funext x; simp [ouTriple, Go, mul_comm]
  Γ_add_A := fun f hf f' hf' g _ => by
    funext x; simp [ouTriple, Go, deriv_add_s hf hf', add_mul]
  Γ_smul_A := fun c f hf g _ => by
    funext x; simp [ouTriple, Go, deriv_smul_s c hf, mul_assoc]
  Γ_nonneg_A := fun f _ x => by simpa [ouTriple, Go] using mul_self_nonneg (deriv f x)
  L_add_A := fun f hf g hg => Lo_add hf hg
  L_smul_A := fun c f hf => Lo_smul c hf
  carre_du_champ_A := fun f hf g hg x => by
    show deriv f x * deriv g x = (Lo (f * g) x - f x * Lo g x - g x * Lo f x) / 2
    rw [Lo_mul hf hg x]; ring
  diffusion_A := fun k ψ hψ f hf =>
    ⟨fun g hg => (diffusion_s k ψ hψ f hf).1 g hg, (diffusion_s k ψ hψ f hf).2⟩
  esa := ou_esa
  ibp_A := fun f hf _ _ g hg => ⟨integrable_Γ_cs hf hg, by
    show ∫ x, g x * Lo f x ∂γ = -∫ x, Go f g x ∂γ
    rw [ibp_cs_left hf hg, Go_comm_integral]⟩
  ibp_A_symm := fun f hf _ _ g hg => by
    have := ibp_cs_right hf hg
    exact this
  ibp_AA := fun f hf k hk h1 h2 h3 h4 h5 => ou_ibp_AA hf hk h1 h2 h3 h4 h5
  semigroup_stable := fun P hP t f hf u hu => ou_semigroup_stable hP t f hf u hu

/-- `CD(1,∞)` on the extended algebra `C^∞(ℝ)`. -/
theorem ouFull_CDFull : ouFull.CDFull 1 ∞ :=
  ⟨by simp, fun f hf => Filter.Eventually.of_forall fun x => ou_CD_pt (show Sm f from hf) x⟩

instance : IsProbabilityMeasure ouFull.μ := by
  show IsProbabilityMeasure γ
  infer_instance

/-- the full triple has `Γ ≠ 0` (witness `f = id`). -/
theorem ouFull_Γ_ne_zero : ouFull.Γ (fun x => x) (fun x => x) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [ouFull, ouTriple, Go] at this

/-- **The Gaussian Poincaré inequality `PI(1)` for OU**, obtained by instantiating the abstract
Bakry–Émery theorem `poincare_of_CD_infty` on the Ornstein–Uhlenbeck full triple. -/
theorem ou_poincare : ouFull.toMarkovTriple.PoincareIneq (1 / 1) :=
  Hilbert.poincare_of_CD_infty ouFull one_pos ou_CD ou_ergodic

end MarkovTriple.Sanity.OU

#print axioms MarkovTriple.Sanity.OU.ouFull
#print axioms MarkovTriple.Sanity.OU.ouFull_CDFull
#print axioms MarkovTriple.Sanity.OU.ou_ergodic
#print axioms MarkovTriple.Sanity.OU.ou_poincare
