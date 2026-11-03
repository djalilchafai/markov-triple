import Mathlib
import MarkovTriple.BGL.Theory.Extension.Ident

/-!
# Prop. 3.3.16 (v), first statement (BGL p. 160): for `g, h ∈ 𝒜₀`, `a_k → f` in `𝒟(L)` ⇒ `H(a_k)(g,h)` converges in `L²`

`hess2_exists`: the `L²`-limit exists and is independent of the sequence (bound
`∫ H(a)(g,h)² ≤ ‖Γ g‖_∞ ‖Γ h‖_∞ ∫ (Γ₂(a) − ρΓ(a))`, from (3.3.7)); its limit coincides a.e. with `hessE` (second conjunct of `hess2_exists`; the name `hess2_eq_hessE` of STATEMENTS_R14.md never existed, see ERRATA E5).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- the `L²`-class of `H(a)(g,h)`, `a,g,h ∈ 𝒜₀`. -/
noncomputable def HH2 (T : FullTriple E) (a g h : T.A₀) : Lp ℝ 2 T.μ :=
  (DiffusionTriple.memLp2 T.toDiffusionTriple
    (Hess_memA₀ (A₀_memA a.2) (A₀_memA g.2) h.2)).toLp (Hess T a.1 g.1 h.1)

lemma HH2_ae (a g h : T.A₀) : (HH2 T a g h : E → ℝ) =ᵐ[T.μ] Hess T a.1 g.1 h.1 :=
  MemLp.coeFn_toLp _

lemma HH2_sub (a a' g h : T.A₀) : HH2 T (a - a') g h = HH2 T a g h - HH2 T a' g h := by
  refine Lp.ext ?_
  filter_upwards [HH2_ae (a - a') g h, HH2_ae a g h, HH2_ae a' g h,
    Lp.coeFn_sub (HH2 T a g h) (HH2 T a' g h),
    Hess_lin_left (A₀_memA a.2) (A₀_memA a'.2) (A₀_memA g.2) (A₀_memA h.2) (-1)] with x e1 e2 e3 e4 e5
  rw [e4, Pi.sub_apply, e1, e2, e3, coe_sub']
  rw [e5]; ring

lemma HH2_bound {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (g h : T.A₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : T.A₀, ‖HH2 T a g h‖ ≤ C * ‖jL T a‖ := by
  obtain ⟨Bg, hBg⟩ := T.bounded (G T g.1 g.1) (T.ΓA_self_mem_A₀ g.2)
  obtain ⟨Bh, hBh⟩ := T.bounded (G T h.1 h.1) (T.ΓA_self_mem_A₀ h.2)
  set B : ℝ := |Bg| * |Bh| with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨√(B * (2 * (1 + |ρ|))), Real.sqrt_nonneg _, fun a => ?_⟩
  have iK := integrable_A₀ (Kf_memA₀ (T := T) ρ a.2)
  have hHm := Hess_memA₀ (T := T) (A₀_memA a.2) (A₀_memA g.2) h.2
  have iH2 : Integrable (fun x => (Hess T a.1 g.1 h.1 x) ^ 2) T.μ :=
    (DiffusionTriple.memLp2 T.toDiffusionTriple hHm).integrable_sq
  have h1 : ‖HH2 T a g h‖ ^ 2 = ∫ x, (Hess T a.1 g.1 h.1 x) ^ 2 ∂T.μ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [HH2_ae a g h] with x hx
    rw [hx]; ring
  have hineq := hessian_general_ineq hCD (A₀_memA a.2) (A₀_memA g.2) (A₀_memA h.2)
  have hK0 := Kf_nonneg hCD a.1 (A₀_memA a.2)
  have hg0 := T.ΓA_nonneg _ (A₀_memA g.2)
  have hh0 := T.ΓA_nonneg _ (A₀_memA h.2)
  have h2 : ∫ x, (Hess T a.1 g.1 h.1 x) ^ 2 ∂T.μ ≤ B * ∫ x, Kf T ρ a.1 a.1 x ∂T.μ := by
    rw [← integral_const_mul]
    refine integral_mono_ae iH2 (iK.const_mul B) ?_
    filter_upwards [hineq, hK0, hg0, hh0] with x e1 e2 e3 e4
    simp only [Pi.zero_apply] at e2 e3 e4
    refine e1.trans ?_
    have p1 : G T g.1 g.1 x ≤ |Bg| := (le_abs_self _).trans ((hBg x).trans (le_abs_self Bg))
    have p2 : G T h.1 h.1 x ≤ |Bh| := (le_abs_self _).trans ((hBh x).trans (le_abs_self Bh))
    have : G T g.1 g.1 x * G T h.1 h.1 x ≤ B := mul_le_mul p1 p2 e4 (abs_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left this e2]
  have h3 : ∫ x, Kf T ρ a.1 a.1 x ∂T.μ ≤ 2 * (1 + |ρ|) * ‖jL T a‖ ^ 2 := by
    refine (eK_le ρ a).trans ?_
    have := graphSq_le a
    nlinarith [abs_nonneg ρ]
  have h4 : ‖HH2 T a g h‖ ^ 2 ≤ (B * (2 * (1 + |ρ|))) * ‖jL T a‖ ^ 2 := by
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left h3 hB0]
  have h5 : 0 ≤ B * (2 * (1 + |ρ|)) := by positivity
  calc ‖HH2 T a g h‖ = √(‖HH2 T a g h‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √((B * (2 * (1 + |ρ|))) * ‖jL T a‖ ^ 2) := Real.sqrt_le_sqrt h4
    _ = √(B * (2 * (1 + |ρ|))) * ‖jL T a‖ := by
        rw [Real.sqrt_mul h5, Real.sqrt_sq (norm_nonneg _)]

/-- **BGL Prop. 3.3.16 (v), first statement**: `H(a_k)(g,h)` converges in `L²`, with a limit independent of the
graph-convergent sequence `a_k → f`; the limit is the extended Hessian. -/
theorem hess2_exists {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (g h : T.A₀) :
    ∃ H₂ : Lp ℝ 2 T.μ, (∀ a : ℕ → T.A₀, GraphConv T a u hu →
      Tendsto (fun k => HH2 T (a k) g h) atTop (𝓝 H₂)) ∧
      (H₂ : E → ℝ) =ᵐ[T.μ] (hessE hCD u hu (T.toDiffusionTriple.clsQ g) h : E → ℝ) := by
  obtain ⟨C, hC0, hC⟩ := HH2_bound hCD g h
  have cauchy : ∀ a : ℕ → T.A₀, GraphConv T a u hu → CauchySeq (fun k => HH2 T (a k) g h) := by
    intro a ha
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have c1 := cauchySeq_iff_tendsto_dist_atTop_0.1 (Tendsto.cauchySeq ha)
    have lim := c1.const_mul C
    simp only [mul_zero] at lim
    refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) lim
    rw [dist_eq_norm, ← HH2_sub]
    refine (hC _).trans ?_
    rw [map_sub, ← dist_eq_norm]
  obtain ⟨a0, ha0⟩ := exists_graphConv u hu
  obtain ⟨H₂, hH₂⟩ := cauchySeq_tendsto_of_complete (cauchy a0 ha0)
  have uniq : ∀ a : ℕ → T.A₀, GraphConv T a u hu →
      Tendsto (fun k => HH2 T (a k) g h) atTop (𝓝 H₂) := by
    intro a ha
    obtain ⟨H', hH'⟩ := cauchySeq_tendsto_of_complete (cauchy a ha)
    have hd : Tendsto (fun k => dist (HH2 T (a k) g h) (HH2 T (a0 k) g h)) atTop (𝓝 0) := by
      have h1 := tendsto_iff_dist_tendsto_zero.1 ha
      have h2 := tendsto_iff_dist_tendsto_zero.1 ha0
      have lim := ((h1.add h2).const_mul C)
      simp only [add_zero, mul_zero] at lim
      refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) lim
      rw [dist_eq_norm, ← HH2_sub]
      refine (hC _).trans ?_
      rw [map_sub, ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (dist_triangle_right _ _ _) hC0
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    refine squeeze_zero (fun k => dist_nonneg) (fun k => dist_triangle _ (HH2 T (a0 k) g h) _) ?_
    simpa using hd.add (tendsto_iff_dist_tendsto_zero.1 hH₂)
  refine ⟨H₂, uniq, ?_⟩
  have s2 := hessE_tendsto hCD h ha0 (formConv_const g)
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨φ, hφ, a1, a2⟩ := Lp_ae_subseq_two hH₂ s2
  have hall : ∀ᵐ x ∂T.μ, ∀ m, (HH2 T (a0 m) g h : E → ℝ) x = (HH T (a0 m) g h : E → ℝ) x := by
    rw [ae_all_iff]; intro m
    filter_upwards [HH2_ae (a0 m) g h, HH_ae (a0 m) g h] with x e1 e2
    rw [e1, e2]
  filter_upwards [a1, a2, hall] with x e1 e2 e3
  exact tendsto_nhds_unique e1 (e2.congr (fun m => (e3 (φ m)).symm))

end FullTriple

end MarkovTriple.BGL
