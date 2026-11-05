import Mathlib
import MarkovTriple.Stochastic.R30.GaussMeasure
import MarkovTriple.Stochastic.R30.MehlerL2
import MarkovTriple.Stochastic.R30.Duhamel

/-!
# Round 30 (S), part 7: the Friedrichs semigroup of `gaussRdFull d` is the Mehler semigroup on the test class

For `f ∈ C_c^∞(ℝ^d)` and `t ≥ 0`: `P_t [f] = [Gm f t]` in `L²(γ_d)`, where `Gm f t (x) = ∫ f(e^{-t} x + √(1-e^{-2t}) y) dγ(y)`.

Route (BGL Sect. 2.7.1; no Hermite completeness in dimension `d`): the abstract Duhamel uniqueness `duhamel_unique` applied to `Q s = [Gm f s]`.
Its hypotheses: continuity and the strong derivative `d/ds Q s = [Lou (Gm f s)]` (`MehlerL2`), and the Green identity
`⟨L̄ v, Q s⟩ = ⟨v, Lou Q s⟩` for `v ∈ 𝒟(L̄)`, proved here from the core property F10 of the Full triple and integration by parts for `a ∈ C_c^∞`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.Stochastic.R30

open MarkovTriple.BGL MarkovTriple.BGL.LebesgueRd
open MarkovTriple.BGL.Instances.GibbsRd (gaussData qd sm_qd pderiv_qd Lr GibbsRdData EllData)

variable {d : ℕ} {φ : (Fin d → ℝ) → ℝ}

/-- `Lr` for the Gaussian potential is the Ornstein-Uhlenbeck generator `Lou` -/
lemma gauss_L_eq (f : (Fin d → ℝ) → ℝ) (hf : Sm f) :
    (gaussData d).toEll.L f = Lou f := by
  rw [(gaussData d).toEll_L hf]
  funext x
  have h1 : ∀ i, pderiv (fun y : Fin d → ℝ => qd y / 2) i = fun y => y i := by
    intro i
    funext y
    have := pderiv_qd i y
    unfold pderiv at this ⊢
    have hd : HasFDerivAt (qd : (Fin d → ℝ) → ℝ) (fderiv ℝ qd y) y :=
      (sm_qd.differentiableAt y).hasFDerivAt
    rw [show (fun y : Fin d → ℝ => qd y / 2) = fun y => (2 : ℝ)⁻¹ * qd y from by
      funext z; simp [div_eq_inv_mul], (hd.const_mul (2 : ℝ)⁻¹).fderiv]
    simp [this]
  have hV : (gaussData d).V = fun y : Fin d → ℝ => qd y / 2 := rfl
  unfold Lr Lou
  rw [hV, Finset.sum_sub_distrib]
  simp only [h1]
  rfl

/-- the Ornstein-Uhlenbeck reference measure is `γ_d` (`S1`), as a hypothesis-free name -/
lemma hμ (d : ℕ) : (gaussRdFull d).toDiffusionTriple.μ = gam d := gaussRdFull_mu d

section generic

variable {ν : Measure (Fin d → ℝ)}

lemma memLp_Gm_ν (hν : ν = gam d) (hφ : φ ∈ A₀ d) (σ : ℝ) : MemLp (Gm φ σ) 2 ν :=
  hν ▸ memLp_Gm hφ σ

lemma memLp_Lou_ν (hν : ν = gam d) (hφ : φ ∈ A₀ d) (σ : ℝ) : MemLp (Lou (Gm φ σ)) 2 ν :=
  hν ▸ memLp_Lou_Gm hφ σ

/-- the Mehler flow in `L²(ν)`, `ν = γ_d` -/
noncomputable def Qν (hν : ν = gam d) (hφ : φ ∈ A₀ d) (σ : ℝ) : Lp ℝ 2 ν :=
  (memLp_Gm_ν hν hφ σ).toLp (Gm φ σ)

/-- its time derivative -/
noncomputable def DQν (hν : ν = gam d) (hφ : φ ∈ A₀ d) (σ : ℝ) : Lp ℝ 2 ν :=
  (memLp_Lou_ν hν hφ σ).toLp (Lou (Gm φ σ))

theorem hasDerivAt_Qν (hν : ν = gam d) (hφ : φ ∈ A₀ d) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Qν hν hφ) (DQν hν hφ s) s := by
  subst hν; exact hasDerivAt_Qcls hφ hs

theorem continuous_Qν (hν : ν = gam d) (hφ : φ ∈ A₀ d) : Continuous (Qν hν hφ) := by
  subst hν; exact continuous_Qcls hφ

end generic

/-- the Green identity on test functions: `∫ (L a) w dμ = ∫ a (L w) dμ` for `a ∈ C_c^∞`, `w` smooth -/
lemma integral_L_mul_symm {a w : (Fin d → ℝ) → ℝ} (ha : a ∈ A₀ d) (hw : Sm w) :
    ∫ x, (gaussData d).toEll.L a x * w x ∂(gaussData d).toEll.μ =
      ∫ x, a x * (gaussData d).toEll.L w x ∂(gaussData d).toEll.μ := by
  set E := (gaussData d).toEll with hE
  have e1 := E.ibp_sm (f := a) (g := w) ha.1 hw (Or.inr ha.2)
  have e2 := E.ibp_sm (f := w) (g := a) hw ha.1 (Or.inl ha.2)
  rw [E.Γ_symm w a] at e1
  have h3 : ∫ x, E.L a x * w x ∂E.μ = ∫ x, w x * E.L a x ∂E.μ :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [h3, e1, e2]

/-- **Green identity** for the Friedrichs generator of `gaussRdFull d` against the Mehler flow -/
theorem green_Qν (hφ : φ ∈ A₀ d) {s : ℝ} (v : Lp ℝ 2 (gaussRdFull d).toDiffusionTriple.μ)
    (hv : v ∈ (gaussRdFull d).toDiffusionTriple.generator.domain) :
    inner ℝ ((gaussRdFull d).toDiffusionTriple.generator ⟨v, hv⟩) (Qν (hμ d) hφ s) =
      inner ℝ v (DQν (hμ d) hφ s) := by
  have hw : Sm (Gm φ s) := Mh_smooth hφ _ _
  obtain ⟨a, h1, h2⟩ := (gaussRdFull d).esa v hv
  have hn : ∀ n, inner ℝ ((gaussRdFull d).toDiffusionTriple.Lcls (a n)) (Qν (hμ d) hφ s) = inner ℝ ((gaussRdFull d).toDiffusionTriple.cls (a n)) (DQν (hμ d) hφ s) := by
    intro n
    rw [L2_inner_eq, L2_inner_eq]
    have hLw : (gaussData d).toEll.L (Gm φ s) = Lou (Gm φ s) := gauss_L_eq _ hw
    have := integral_L_mul_symm (a := (a n).1) (w := Gm φ s) (a n).2 hw
    rw [hLw] at this
    refine Eq.trans ?_ (this.trans ?_)
    · refine integral_congr_ae ?_
      filter_upwards [DiffusionTriple.coeFn_Lcls (gaussRdFull d).toDiffusionTriple (a n), (memLp_Gm_ν (hμ d) hφ s).coeFn_toLp] with x h1 h2
      show (gaussRdFull d).toDiffusionTriple.Lcls (a n) x * (memLp_Gm_ν (hμ d) hφ s).toLp (Gm φ s) x = _
      rw [h1, h2]
      rfl
    · refine integral_congr_ae ?_
      filter_upwards [DiffusionTriple.coeFn_cls (gaussRdFull d).toDiffusionTriple (a n), (memLp_Lou_ν (hμ d) hφ s).coeFn_toLp] with x h1 h2
      show _ = (gaussRdFull d).toDiffusionTriple.cls (a n) x * (memLp_Lou_ν (hμ d) hφ s).toLp (Lou (Gm φ s)) x
      rw [h1, h2]
  have t1 : Tendsto (fun n => inner ℝ ((gaussRdFull d).toDiffusionTriple.Lcls (a n)) (Qν (hμ d) hφ s)) atTop
      (𝓝 (inner ℝ ((gaussRdFull d).toDiffusionTriple.generator ⟨v, hv⟩) (Qν (hμ d) hφ s))) := h2.inner tendsto_const_nhds
  have t2 : Tendsto (fun n => inner ℝ ((gaussRdFull d).toDiffusionTriple.cls (a n)) (DQν (hμ d) hφ s)) atTop
      (𝓝 (inner ℝ v (DQν (hμ d) hφ s))) := h1.inner tendsto_const_nhds
  exact tendsto_nhds_unique t1 (t2.congr fun n => (hn n).symm)

lemma Qν_zero (hφ : φ ∈ A₀ d) :
    Qν (hμ d) hφ 0 = (gaussRdFull d).toDiffusionTriple.cls ⟨φ, hφ⟩ := by
  refine Lp.ext ?_
  filter_upwards [(memLp_Gm_ν (hμ d) hφ 0).coeFn_toLp,
    DiffusionTriple.coeFn_cls (gaussRdFull d).toDiffusionTriple ⟨φ, hφ⟩] with x h1 h2
  show (memLp_Gm_ν (hμ d) hφ 0).toLp (Gm φ 0) x = _
  rw [h1, h2, Gm_zero]

/-- **Mehler formula for the Friedrichs semigroup of `gaussRdFull d`**: `P_t [φ] = [Gm φ t]` in `L²(γ_d)`, `φ ∈ C_c^∞`. -/
theorem gaussRdFull_semigroup_eq_Q (hφ : φ ∈ A₀ d) (t : ℝ≥0) :
    (gaussRdFull d).toDiffusionTriple.semigroup t ((gaussRdFull d).toDiffusionTriple.cls ⟨φ, hφ⟩) =
      Qν (hμ d) hφ t := by
  rw [← Qν_zero hφ]
  exact duhamel_unique (gaussRdFull d).toDiffusionTriple (Qν (hμ d) hφ) (DQν (hμ d) hφ)
    (continuous_Qν (hμ d) hφ) (fun s hs => hasDerivAt_Qν (hμ d) hφ hs)
    (fun s _ v hv => green_Qν hφ v hv) t

end MarkovTriple.Stochastic.R30
