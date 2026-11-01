import Mathlib
import MarkovTriple.FunctionalInequalities.Poincare
import MarkovTriple.Frozen.Poincare

/-!
# Extension of the Poincaré inequality from `𝒜₀` to the form domain `Q`

* `FormData.gap_Q_of_D` (abstract): if `ρ (‖f‖² − ⟪f,e⟫²) ≤ ⟪A f, f⟫` on the core `D`, the same holds on
  the form domain `Q` with `⟪A f,f⟫` replaced by the closed form `E`.  Proof: both sides are
  continuous on the energy Hilbert space `K` (the completion of `D`), and `D` is dense in `K`.
* `Hilbert.rho_variance_le_energy_Q` : for a probability measure and `ρ Var(g) ≤ ∫Γ(g,g)` on `𝒜₀`,
  `ρ Var(u) ≤ E(u,u)` for every `u ∈ Q` (here `Var(u) = ‖u‖² − (∫u)²`).
* `Hilbert.hasSpectralGap_of_poincare` : `PoincareIneq C`, `C > 0` ⇒ `HasSpectralGap (1/C)` for the
  Friedrichs form of a full Markov triple (uses only `⟪u,1⟫ = 0`, i.e. `R 1 = 1`).
* `Hilbert.expDecay_of_poincare` : `‖P_t u‖ ≤ e^{−t/C} ‖u‖` for `u ⟂ 1` under `ErgodicL2`
  (via `hasExpDecay_of_hasSpectralGap`).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- Extension of a Poincaré-type inequality from the core `D` to the form domain `Q`. -/
theorem gap_Q_of_D (e : H) (ρ : ℝ)
    (h : ∀ f : S.D, ρ * (‖(f : H)‖ ^ 2 - inner ℝ (f : H) e ^ 2) ≤ inner ℝ (S.A f) (f : H))
    (u : S.Q) :
    ρ * (‖(u : H)‖ ^ 2 - inner ℝ (u : H) e ^ 2) ≤ S.E u u := by
  obtain ⟨x, rfl⟩ := S.qEquiv.surjective u
  have key : ∀ y : S.K, ρ * (‖S.ι y‖ ^ 2 - inner ℝ (S.ι y) e ^ 2) ≤
      inner ℝ y y - inner ℝ (S.ι y) (S.ι y) := by
    intro y
    refine UniformSpace.Completion.induction_on y (isClosed_le (by fun_prop) (by fun_prop)) ?_
    intro f
    rw [UniformSpace.Completion.inner_coe, S.ι_coe, S.inner_dom]
    have := h f
    rw [real_inner_self_eq_norm_sq] at *
    simp only [emb_apply, opA_apply] at *
    linarith
  have := key x
  rw [S.E_eq, qEquiv_apply]
  rw [real_inner_self_eq_norm_sq] at this ⊢
  simpa [real_inner_self_eq_norm_sq] using this

end FormData

variable {E : Type*} [MeasurableSpace E]

/-- The class of the constant `1` in `L²(μ)`. -/
noncomputable def oneL2 (μ : Measure E) [IsFiniteMeasure μ] : Lp ℝ 2 μ :=
  (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ))

lemma variance_Lp (μ : Measure E) [IsProbabilityMeasure μ] (u : Lp ℝ 2 μ) :
    ProbabilityTheory.variance (u : E → ℝ) μ = ‖u‖ ^ 2 - inner ℝ u (oneL2 μ) ^ 2 := by
  rw [ProbabilityTheory.variance_eq_sub (Lp.memLp u)]
  have h1 : inner ℝ u (oneL2 μ) = ∫ x, u x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have h0 : ((oneL2 μ : Lp ℝ 2 μ) : E → ℝ) =ᵐ[μ] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    filter_upwards [h0] with x hx
    rw [hx]; simp
  have h2 : ‖u‖ ^ 2 = ∫ x, (u x) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sq]
  rw [h1, h2]
  rfl

/-- **Poincaré inequality on the form domain.**  If `ρ Var(g) ≤ ∫ Γ(g,g)` on `𝒜₀`
(`μ` probability), then `ρ Var(u) ≤ E(u,u)` for all `u ∈ Q`. -/
theorem rho_variance_le_energy_Q (T : _root_.MarkovTriple E) [IsProbabilityMeasure T.μ] {ρ : ℝ}
    (h : ∀ g ∈ T.A₀, ρ * ProbabilityTheory.variance g T.μ ≤ ∫ x, T.Γ g g x ∂T.μ)
    (u : (formData T).Q) :
    ρ * ProbabilityTheory.variance ((u : Lp ℝ 2 T.μ) : E → ℝ) T.μ ≤ (formData T).E u u := by
  rw [variance_Lp]
  refine (formData T).gap_Q_of_D (oneL2 T.μ) ρ ?_ u
  rintro ⟨_, g, rfl⟩
  have hg := h g.1 g.2
  have e1 : inner ℝ (formA T ⟨toLp0 T g, ⟨g, rfl⟩⟩) (toLp0 T g) = ∫ x, T.Γ g.1 g.1 x ∂T.μ :=
    inner_formA T g g
  have e2 := variance_Lp T.μ (toLp0 T g)
  have e3 : ProbabilityTheory.variance (toLp0 T g : E → ℝ) T.μ =
      ProbabilityTheory.variance g.1 T.μ :=
    ProbabilityTheory.variance_congr (coeFn_toLp0 T g)
  rw [← e2, e3]
  exact e1 ▸ hg

/-- The constant `1` is a fixed vector of the Friedrichs resolvent of a full Markov triple on a
finite measure space (`resolvent_eq`, `L 1 = 0`). -/
lemma R_oneL2 (F : FullMarkovTriple E) [IsFiniteMeasure F.μ] :
    (formData F.toMarkovTriple).R (oneL2 F.μ) = oneL2 F.μ := by
  have h1 : MemLp (1 : E → ℝ) 2 F.μ := memLp_const 1
  have hL : MemLp (F.L (1 : E → ℝ)) 2 F.μ := by rw [F.L_one]; exact MemLp.zero
  have key := F.resolvent_eq F.A.one_mem h1 hL
  have hv : hL.toLp (F.L (1 : E → ℝ)) = 0 := by
    refine Lp.ext ?_
    filter_upwards [hL.coeFn_toLp, Lp.coeFn_zero ℝ 2 F.μ] with x e1 e2
    rw [e1, e2]; simp [F.L_one]
  rw [hv, sub_zero] at key
  exact key

/-- **`PoincareIneq C` ⟹ `HasSpectralGap (1/C)`** for the Friedrichs form of a full Markov triple
(`μ` probability, `C > 0`): the Poincaré inequality extends from `𝒜₀` to the form domain `Q`
(`rho_variance_le_energy_Q`) and `u ⟂ 1` kills the mean. -/
theorem hasSpectralGap_of_poincare (F : FullMarkovTriple E) {C : ℝ} (hC : 0 < C)
    (hP : F.toMarkovTriple.PoincareIneq C) :
    (formData F.toMarkovTriple).HasSpectralGap (1 / C) := by
  have : IsProbabilityMeasure F.μ := hP.1
  intro u hu
  have hg : ∀ g ∈ F.A₀, (1 / C) * ProbabilityTheory.variance g F.μ ≤ ∫ x, F.Γ g g x ∂F.μ := by
    intro g hg
    have := hP.2 g hg
    have h2 : ProbabilityTheory.variance g F.μ ≤ C * ∫ x, F.Γ g g x ∂F.μ := this
    rw [one_div, inv_mul_le_iff₀ hC]
    exact h2
  have h := rho_variance_le_energy_Q F.toMarkovTriple hg u
  rw [variance_Lp] at h
  have h0 : inner ℝ ((u : Lp ℝ 2 F.μ)) (oneL2 F.μ) = 0 := hu _ (R_oneL2 F)
  rw [h0] at h
  simpa using h

/-- **`PoincareIneq C` ⟹ `Var(u) ≤ C E(u,u)` for every `u ∈ Q`.** -/
theorem variance_le_energy_Q (F : FullMarkovTriple E) {C : ℝ} (hC : 0 < C)
    (hP : F.toMarkovTriple.PoincareIneq C) (u : (formData F.toMarkovTriple).Q) :
    ProbabilityTheory.variance ((u : Lp ℝ 2 F.μ) : E → ℝ) F.μ ≤ C * (formData F.toMarkovTriple).E u u := by
  have : IsProbabilityMeasure F.μ := hP.1
  have hg : ∀ g ∈ F.A₀, (1 / C) * ProbabilityTheory.variance g F.μ ≤ ∫ x, F.Γ g g x ∂F.μ := by
    intro g hg
    have h2 : ProbabilityTheory.variance g F.μ ≤ C * ∫ x, F.Γ g g x ∂F.μ := hP.2 g hg
    rw [one_div, inv_mul_le_iff₀ hC]
    exact h2
  have h := rho_variance_le_energy_Q F.toMarkovTriple hg u
  rw [one_div, inv_mul_le_iff₀ hC] at h
  exact h

/-- **Exponential decay from Poincaré**: under `ErgodicL2`, `PoincareIneq C` (`C > 0`) gives
`‖P_t u‖ ≤ e^{-t/C} ‖u‖` for every `u ∈ L²` orthogonal to the constants, where
`P_t = tripleSemigroup` is the Friedrichs semigroup. -/
theorem expDecay_of_poincare (F : FullMarkovTriple E) [IsProbabilityMeasure F.μ] {C : ℝ} (hC : 0 < C)
    (hP : F.toMarkovTriple.PoincareIneq C) (herg : F.toMarkovTriple.ErgodicL2)
    (u : Lp ℝ 2 F.μ) (hu : inner ℝ u (oneL2 F.μ) = 0) (t : ℝ≥0) :
    ‖tripleSemigroup F.toMarkovTriple t u‖ ≤ Real.exp (-(1 / C) * t) * ‖u‖ := by
  have hgap := hasSpectralGap_of_poincare F hC hP
  have hdec := (formData F.toMarkovTriple).hasExpDecay_of_hasSpectralGap
    (by positivity) hgap
  refine hdec u ?_ t
  intro n hn
  obtain ⟨c, hc⟩ := fixed_const F herg n hn
  have hnc : n = c • oneL2 F.μ := by
    refine Lp.ext ?_
    have h0 : ((oneL2 F.μ : Lp ℝ 2 F.μ) : E → ℝ) =ᵐ[F.μ] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    filter_upwards [hc, Lp.coeFn_smul c (oneL2 F.μ), h0] with x h1 h2 h3
    rw [h1, h2]; simp [h3]
  rw [hnc, inner_smul_right, hu, mul_zero]

end MarkovTriple.Hilbert
