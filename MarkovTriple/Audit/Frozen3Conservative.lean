import MarkovTriple.Hilbert.FullBridge
import MarkovTriple.Hilbert.MarkovCriterion
import MarkovTriple.Frozen.Energy
/-! # Round-3 audit (G1): the Friedrichs semigroup of a bare `MarkovTriple` need not be conservative.

`not_conservative_of_dirichlet_poincare`: if `μ` is finite and nonzero and the test algebra satisfies a
Dirichlet–Poincaré inequality `∫ f² ≤ c ∫ Γ(f,f)` (true for `C_c^∞(0,1)` with Lebesgue measure and
`Γ(f,g) = f'g'`, with `c = 1/2`, because `f(x)² ≤ x ∫ f'²`), then the Friedrichs semigroup does NOT
satisfy the frozen Markov clause `P_t 1 = 1`.  Proof: `P_t 1 = 1` forces `1 ∈ D(A_F)`, `A_F 1 = 0`,
hence `1 ∈ Q`, `E(1) = 0`; approximating `1` by `f_n ∈ 𝒜₀` with `E(f_n) → 0` and using the inequality
gives `‖1‖ = 0`.  (Not imported by the root.) -/
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E]

open Classical in
theorem not_conservative_of_dirichlet_poincare (T : _root_.MarkovTriple E) [IsFiniteMeasure T.μ]
    (hμ : T.μ Set.univ ≠ 0) (c : ℝ)
    (hc : ∀ g ∈ T.A₀, ∫ x, g x ^ 2 ∂T.μ ≤ c * T.energy g) :
    ¬ (∀ (t : ℝ≥0) (u : Lp ℝ 2 T.μ), (u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ) →
      (tripleSemigroup T t u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ)) := by
  intro hone
  set S := formData T with hS
  have h1 : MemLp (1 : E → ℝ) 2 T.μ := memLp_const 1
  set u : Lp ℝ 2 T.μ := h1.toLp 1 with hu
  have hu1 : (u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ) := h1.coeFn_toLp
  have hPu : ∀ t : ℝ≥0, S.semigroup t u = u := fun t => by
    refine Lp.ext ?_
    exact (hone t u hu1).trans hu1.symm
  -- generator of `u` is `0`
  have hgen : (∃ h : u ∈ S.generator.domain, S.generator ⟨u, h⟩ = 0) := by
    refine (S.tendsto_generator_iff u 0).2 ?_
    refine tendsto_const_nhds.congr (fun t => ?_)
    simp [show S.semigroup t u = u from hPu t]
  obtain ⟨hd, hg0⟩ := hgen
  have hRu : S.R u = u := by
    have := (S.generator_apply_eq_iff hd 0).1 hg0
    simpa using this
  have huQ : u ∈ S.Q := by rw [← hRu]; exact S.R_mem_Q u
  -- `E(u,u) = 0`
  have hE0 : S.E ⟨u, huQ⟩ ⟨u, huQ⟩ = 0 := by
    have h := S.E_R u ⟨u, huQ⟩
    have e : (⟨S.R u, S.R_mem_Q u⟩ : S.Q) = ⟨u, huQ⟩ := Subtype.ext hRu
    rw [e, hRu] at h
    simpa using h
  -- approximate
  set D := S.dirFriedrichs with hD
  obtain ⟨f, hf, hfc⟩ := (D.mem_Q _).1 (show u ∈ D.Q from huQ)
  have hlim := D.E_lim f f u u hf hfc hf hfc
  have hEu : D.E u u = 0 := by
    have : D.E u u = S.E ⟨u, huQ⟩ ⟨u, huQ⟩ := by
      show (if h : u ∈ S.Q ∧ u ∈ S.Q then S.E ⟨u, h.1⟩ ⟨u, h.2⟩ else 0) = _
      rw [dif_pos (show u ∈ S.Q ∧ u ∈ S.Q from ⟨huQ, huQ⟩)]
    rw [this, hE0]
  rw [hEu] at hlim
  have hineq : ∀ n, ‖(f n : Lp ℝ 2 T.μ)‖ ^ 2 ≤ c * S.en (f n) (f n) := fun n => by
    obtain ⟨d, hdmem⟩ := f n
    obtain ⟨g, rfl⟩ := hdmem
    have e1 : S.en ⟨toLp0 T g, ⟨g, rfl⟩⟩ ⟨toLp0 T g, ⟨g, rfl⟩⟩ = qf T g g := inner_formA T g g
    have e2 : ‖toLp0 T g‖ ^ 2 = ∫ x, g.1 x ^ 2 ∂T.μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_toLp0 T g] with x hx
      rw [hx]; simp [sq]
    show ‖toLp0 T g‖ ^ 2 ≤ _
    rw [e1, e2]
    exact hc g.1 g.2
  have hnorm : Tendsto (fun n => ‖(f n : Lp ℝ 2 T.μ)‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2)) :=
    ((hf.norm).pow 2)
  have hle : ‖u‖ ^ 2 ≤ 0 := by
    have := le_of_tendsto_of_tendsto hnorm (hlim.const_mul c) (Eventually.of_forall hineq)
    simpa using this
  have hu0 : u = 0 := by
    have : ‖u‖ = 0 := by nlinarith [norm_nonneg u, sq_nonneg ‖u‖]
    exact norm_eq_zero.1 this
  have hpos : (0 : ℝ) < ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hu, show (h1.toLp (1 : E → ℝ)) = h1.toLp 1 from rfl,
      inner_toLp_toLp h1 h1]
    have : ∫ x, (1 : E → ℝ) x * (1 : E → ℝ) x ∂T.μ = (T.μ Set.univ).toReal := by
      simp [Measure.real]
    rw [this]
    exact ENNReal.toReal_pos hμ (measure_ne_top _ _)
  rw [hu0] at hpos
  simp at hpos
end MarkovTriple.Hilbert

#print axioms MarkovTriple.Hilbert.not_conservative_of_dirichlet_poincare
