import Mathlib
import MarkovTriple.BGL.Theory.Interp.EntropyDeBruijn
import MarkovTriple.BGL.Theory.Interp.Main
import MarkovTriple.BGL.Theory.Compact.Entropy

/-!
# Entropy interpolation, second derivative: `I(s) = -∫ Λ(g_s) L P_s φ` and its derivative (BGL Prop. 5.7.1)

For a `FullTriple` of finite measure and `φ ∈ 𝒜₀` (bounded: field `bounded` of `DiffusionTriple`), `g_s = ε + P_s φ`:

* `orb_bdd`: `|P_s ψ| ≤ c` (sub-Markov), `Γ_Pt_bdd`: `Γ(P_t φ) ≤ B` for `CD(ρ,n)`, `ρ ≥ 0` (BGL Thm 3.3.18 +
  `Γ φ ∈ 𝒜₀` bounded);
* `entI_eq_neg_pair`: `I(r) = -∫ Λ(g_r) (L P_r φ)` (Green's formula `ibp_bdd`), valid for every `r`;
* `hasDerivAt_entI_pair`: `I'(s) = -(∫ Λ'(g_s)(L P_sφ)² + ∫ Λ(g_s) L L P_sφ)` for `s > 0`
  (differentiation of `∫ F(G_r) V_r` with `G`, `V` `L²`-differentiable, `V` bounded: `Compact.hasDerivAt_pairS`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace
open MarkovTriple.BGL.Compact

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- sub-Markov bound for the orbit of a test function: `|P_s ψ| ≤ c`. -/
lemma orb_bdd (ψ : T.A₀) : ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, Bdd c (T.orb ψ s) := by
  obtain ⟨C0, hC0⟩ := T.bounded ψ.1 ψ.2
  have hc : 0 < max C0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max C0 1, hc, fun s => ?_⟩
  refine ae_abs_semigroup_le T.toDiffusionTriple hc (u := T.toDiffusionTriple.cls ψ) ?_ s.toNNReal
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple ψ] with x hx
  rw [hx]; exact (hC0 x).trans (le_max_left _ _)

/-- `Γ(P_t φ)` is bounded uniformly in `t`: `Γ φ ∈ 𝒜₀` is bounded and `√Γ(P_t φ) ≤ P_t(√Γ φ)` (Thm 3.3.18,
`ρ ≥ 0`). -/
lemma Γ_Pt_bdd {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ) (φ : T.A₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ≥0, ∀ᵐ x ∂T.μ, G T (T.Pt t φ) (T.Pt t φ) x ≤ B := by
  obtain ⟨C0, hC0⟩ := T.bounded _ (T.ΓA_self_mem_A₀ φ.2)
  set c : ℝ := Real.sqrt |C0| + 1 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c ^ 2, by positivity, fun t => ?_⟩
  have hu : ∀ᵐ x ∂T.μ, |(T.sqrtΓcls φ : E → ℝ) x| ≤ c := by
    filter_upwards [T.coeFn_sqrtΓcls φ] with x hx
    rw [hx, abs_of_nonneg (Real.sqrt_nonneg _)]
    have : G T φ.1 φ.1 x ≤ |C0| := (le_abs_self _).trans ((hC0 x).trans (le_abs_self _))
    have := Real.sqrt_le_sqrt this
    linarith
  have hb := ae_abs_semigroup_le T.toDiffusionTriple hc0 hu t
  filter_upwards [T.strong_gradient_bound_unconditional hCD hρ φ t, hb,
    T.ΓA_nonneg _ (T.Pt_mem_A t φ)] with x h1 h2 h3
  have e1 : Real.exp (-ρ * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [NNReal.coe_nonneg t])
  have h4 : (T.toDiffusionTriple.semigroup t (T.sqrtΓcls φ) : E → ℝ) x ≤ c := (le_abs_self _).trans h2
  have h5 : Real.sqrt (G T (T.Pt t φ) (T.Pt t φ) x) ≤ c := by
    refine h1.trans ?_
    calc Real.exp (-ρ * t) * (T.toDiffusionTriple.semigroup t (T.sqrtΓcls φ) : E → ℝ) x
        ≤ Real.exp (-ρ * t) * c := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
      _ ≤ 1 * c := mul_le_mul_of_nonneg_right e1 hc0.le
      _ = c := one_mul c
  have := (Real.sqrt_le_left hc0.le).1 h5
  exact this

variable [IsFiniteMeasure T.μ]

/-- **Green's formula for `P_sφ` against a bounded smooth function of `g_s = ε + P_sφ`**:
`∫ Γ(P_sφ, Ψ(g_s)) = -∫ Ψ(g_s) L P_sφ` (`ibp_bdd`, `Ψ ∈ C^∞` with `Ψ, Ψ'` bounded). -/
theorem ibp_Pt_comp (φ : T.A₀) (ε s : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {K : ℝ}
    (hΨb : ∀ y, |Ψ y| ≤ K) (hΨ'b : ∀ y, |deriv Ψ y| ≤ K) :
    ∫ x, G T (T.Pt s.toNNReal φ) (fun x => Ψ (T.entG φ ε s x)) x ∂T.μ =
      -∫ x, Ψ (T.entG φ ε s x) * T.L (T.Pt s.toNNReal φ) x ∂T.μ := by
  set P := T.Pt s.toNNReal φ with hPdef
  have hP : P ∈ T.A := T.Pt_mem_A _ φ
  have hP2 : MemLp P 2 T.μ := T.Pt_memLp _ φ
  have hQP : hP2.toLp P ∈ T.formDomain := Pt_mem_Q φ s
  have hLP : Integrable (T.L P) T.μ := (memLp_L_Pt φ s).integrable one_le_two
  have hgA := entG_mem_A T φ ε s
  set g := T.entG φ ε s with hg
  set k : E → ℝ := fun x => Ψ (g x) with hk
  have hkA : k ∈ T.A := comp_mem_A T hΨ hgA
  have hk2 : MemLp k 2 T.μ := MemLp.of_bound (T.A_measurable k hkA).aestronglyMeasurable K
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hΨb _)
  have hΓk : Integrable (G T k k) T.μ := by
    refine ((integrable_Γ_Pt φ s).const_mul (K ^ 2)).mono'
      (T.A_measurable _ (G_mem hkA hkA)).aestronglyMeasurable ?_
    filter_upwards [ΓA_comp_comp T hΨ hgA, ΓA_shift T ε hP, T.ΓA_nonneg P hP] with x h1 h2 h3
    have h1' : G T k k x = deriv Ψ (g x) ^ 2 * G T g g x := h1
    have h2' : G T g g x = G T P P x := h2
    have h3' : 0 ≤ G T P P x := h3
    rw [Real.norm_eq_abs, h1', h2', abs_of_nonneg (mul_nonneg (sq_nonneg _) h3')]
    refine mul_le_mul_of_nonneg_right ?_ h3'
    have := hΨ'b (g x)
    nlinarith [abs_nonneg (deriv Ψ (g x)), sq_abs (deriv Ψ (g x))]
  have hQk : hk2.toLp k ∈ T.formDomain := mem_formDomain_of_ESA hkA hk2 hΓk
  obtain ⟨-, hibp⟩ := ibp_bdd hP hP2 hQP hLP hkA hk2 hQk (M := K) (Eventually.of_forall fun x => hΨb _)
  exact hibp

omit [IsFiniteMeasure T.μ] in
/-- `Γ(P, Ψ(g)) = Ψ'(g) Γ(P)` a.e. -/
lemma G_Pt_comp (φ : T.A₀) (ε s : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    G T (T.Pt s.toNNReal φ) (fun x => Ψ (T.entG φ ε s x)) =ᵐ[T.μ]
      fun x => deriv Ψ (T.entG φ ε s x) * G T (T.Pt s.toNNReal φ) (T.Pt s.toNNReal φ) x := by
  have hP : T.Pt s.toNNReal φ ∈ T.A := T.Pt_mem_A _ φ
  have hgA := entG_mem_A T φ ε s
  filter_upwards [ΓA_comp_left T hΨ hgA hP, ΓA_comp_left T (contDiff_const.add contDiff_id :
        ContDiff ℝ (⊤ : ℕ∞) fun r : ℝ => ε + r) hP hP] with x h1 h2
  have a1 : G T (fun x => Ψ (T.entG φ ε s x)) (T.Pt s.toNNReal φ) x =
      deriv Ψ (T.entG φ ε s x) * G T (T.entG φ ε s) (T.Pt s.toNNReal φ) x := h1
  have a2 : G T (T.entG φ ε s) (T.Pt s.toNNReal φ) x =
      deriv (fun r : ℝ => ε + r) (T.Pt s.toNNReal φ x) * G T (T.Pt s.toNNReal φ) (T.Pt s.toNNReal φ) x := h2
  have : deriv (fun r : ℝ => ε + r) (T.Pt s.toNNReal φ x) = 1 := by simp
  rw [G_comm (T := T), a1, a2, this, one_mul]

/-- **`I(r) = -∫ Λ(g_r) L P_r φ`.** -/
theorem entI_eq_neg_pair {φ : T.A₀} {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[T.μ] φ.1)
    (hφ : ∀ x, φ.1 x ≤ M) (C : BE.Cut ε M) (r : ℝ) :
    T.entI φ ε r = -∫ x, C.Λ (T.gcurve φ ε r x) * (T.orb (T.Lt φ) r : E → ℝ) x ∂T.μ := by
  obtain ⟨K1, K2, hK1, hK2, hΛb, hΛ'b, -, -⟩ := cs_facts C.hΛ C.hΛc
  have h := ibp_Pt_comp φ ε r C.hΛ hΛb hΛ'b
  have e1 : T.entI φ ε r = ∫ x, G T (T.Pt r.toNNReal φ) (fun x => C.Λ (T.entG φ ε r x)) x ∂T.μ := by
    unfold entI
    refine integral_congr_ae ?_
    filter_upwards [G_Pt_comp φ ε r C.hΛ, ΓA_shift T ε (T.Pt_mem_A r.toNNReal φ),
      entG_range T φ hε hM h0 hφ r] with x h1 h2 h3
    have h2' : T.toDiffusionTriple.ΓA (T.entG φ ε r) (T.entG φ ε r) x =
        G T (T.Pt r.toNNReal φ) (T.Pt r.toNNReal φ) x := h2
    rw [h1, h2', C.deriv_Λ_eq hε h3, div_eq_inv_mul]
  rw [e1, h]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [T.gcurve_ae φ ε r, L_Pt_ae φ r] with x h1 h2
  rw [h1, h2]

/-- **Differentiation of `I`**: for `s > 0`,
`I'(s) = -(∫ Λ'(g_s)(L P_sφ)² + ∫ Λ(g_s) L(L P_sφ))` (`L P_sφ = P_s Lφ`, `L L P_sφ = P_s L²φ`). -/
theorem hasDerivAt_entI_pair {φ : T.A₀} {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[T.μ] φ.1)
    (hφ : ∀ x, φ.1 x ≤ M) (C : BE.Cut ε M) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (T.entI φ ε)
      (-(∫ x, deriv C.Λ (T.gcurve φ ε s x) * (T.orb (T.Lt φ) s : E → ℝ) x *
          (T.orb (T.Lt φ) s : E → ℝ) x ∂T.μ +
        ∫ x, C.Λ (T.gcurve φ ε s x) * (T.orb (T.Lt (T.Lt φ)) s : E → ℝ) x ∂T.μ)) s := by
  have hf : T.entI φ ε = fun r => -∫ x, C.Λ (T.gcurve φ ε r x) *
      (T.orb (T.Lt φ) r : E → ℝ) x ∂T.μ := funext (entI_eq_neg_pair hε hM h0 hφ C)
  rw [hf]
  obtain ⟨c, hc, hb⟩ := orb_bdd (T := T) (T.Lt φ)
  exact (hasDerivAt_pairS C.hΛ C.hΛc hc.le (T.hasDerivAt_gcurve φ ε hs)
    (T.hasDerivAt_orb (T.Lt φ) hs) hb).neg


end FullTriple

end MarkovTriple.BGL
