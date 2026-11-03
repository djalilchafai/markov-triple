import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2Resolvent
import MarkovTriple.BGL.Instances.Gibbs.Core2Calc

/-!
# Gibbs on `ℝ`: cut-off approximation in the graph norm of `L²` (R17, Stream A)

For `v` smooth with `v, v', v'', v''' ∈ L²(μ)`, `L v, L L v ∈ L²(μ)` and bounded `V', V'', V'''`, the cut-offs `χ_n v`
satisfy `‖χ_n v − v‖, ‖L(χ_n v) − L v‖, ‖L²(χ_n v) − L²v‖ → 0` in `L²(μ)` (dominated convergence; the cut-off commutators of
`Core2Calc.lean` have coefficients bounded uniformly in `n`).  Bookkeeping by the predicates `UB` (uniformly bounded
coefficient families) and `ZL` (sequences tending to `0` in `L²`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL.Lebesgue (chiR Rn Rn_pos chiR_smooth chiR_cs chiR_eq_one_of)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

/-! ### Uniformly bounded coefficient families -/

/-- a family `n ↦ f n : ℝ → ℝ` bounded uniformly in `n` and `x`. -/
def UB (f : ℕ → ℝ → ℝ) : Prop := ∃ C : ℝ, ∀ n x, |f n x| ≤ C

lemma UB.add {f g : ℕ → ℝ → ℝ} (hf : UB f) (hg : UB g) : UB (fun n x => f n x + g n x) := by
  obtain ⟨C, hC⟩ := hf; obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun n x => (abs_add_le _ _).trans (add_le_add (hC n x) (hD n x))⟩

lemma UB.sub {f g : ℕ → ℝ → ℝ} (hf : UB f) (hg : UB g) : UB (fun n x => f n x - g n x) := by
  obtain ⟨C, hC⟩ := hf; obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun n x => (abs_sub _ _).trans (add_le_add (hC n x) (hD n x))⟩

lemma UB.mul {f g : ℕ → ℝ → ℝ} (hf : UB f) (hg : UB g) : UB (fun n x => f n x * g n x) := by
  obtain ⟨C, hC⟩ := hf; obtain ⟨D, hD⟩ := hg
  refine ⟨C * D, fun n x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC n x) (hD n x) (abs_nonneg _) ((abs_nonneg _).trans (hC n x))

lemma UB.const (c : ℝ) : UB (fun _ _ => c) := ⟨|c|, fun _ _ => le_rfl⟩

/-! ### Sequences tending to `0` in `L²` -/

section ZL
variable {μ : Measure ℝ}

/-- `‖[g]‖² = ∫ g²`. -/
lemma norm_toLp_sq' {g : ℝ → ℝ} (hg : MemLp g 2 μ) : ‖hg.toLp g‖ ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]
  simp [sq]

lemma tendsto_toLp_zero {G : ℕ → ℝ → ℝ} (hG : ∀ n, MemLp (G n) 2 μ)
    (h : Tendsto (fun n => ∫ x, (G n x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ n, ‖(hG n).toLp (G n) - 0‖ = Real.sqrt (∫ x, (G n x) ^ 2 ∂μ) := by
    intro n
    rw [sub_zero, ← Real.sqrt_sq (norm_nonneg _), norm_toLp_sq' (hG n)]
  simp only [e]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  exact this

/-- `D n → 0` in `L²(μ)` (with the `L²` memberships). -/
def ZL (μ : Measure ℝ) (D : ℕ → ℝ → ℝ) : Prop :=
  ∃ h : ∀ n, MemLp (D n) 2 μ, Tendsto (fun n => (h n).toLp (D n)) atTop (𝓝 0)

lemma ZL.add {D₁ D₂ : ℕ → ℝ → ℝ} (h₁ : ZL μ D₁) (h₂ : ZL μ D₂) : ZL μ (fun n x => D₁ n x + D₂ n x) := by
  obtain ⟨m₁, t₁⟩ := h₁; obtain ⟨m₂, t₂⟩ := h₂
  refine ⟨fun n => (m₁ n).add (m₂ n), ?_⟩
  have := t₁.add t₂
  rw [add_zero] at this
  refine this.congr (fun n => ?_)
  rw [← MemLp.toLp_add]; rfl

lemma ZL.sub {D₁ D₂ : ℕ → ℝ → ℝ} (h₁ : ZL μ D₁) (h₂ : ZL μ D₂) : ZL μ (fun n x => D₁ n x - D₂ n x) := by
  obtain ⟨m₁, t₁⟩ := h₁; obtain ⟨m₂, t₂⟩ := h₂
  refine ⟨fun n => (m₁ n).sub (m₂ n), ?_⟩
  have := t₁.sub t₂
  rw [sub_zero] at this
  refine this.congr (fun n => ?_)
  rw [← MemLp.toLp_sub]; rfl

lemma ZL.congr {D D' : ℕ → ℝ → ℝ} (h : ZL μ D) (e : ∀ n x, D n x = D' n x) : ZL μ D' := by
  have : D = D' := funext fun n => funext fun x => e n x
  rwa [← this]

/-- bounded continuous coefficients, vanishing eventually at every point, times a fixed `L²` function. -/
lemma ZL.of_mul {c : ℕ → ℝ → ℝ} (hcont : ∀ n, Continuous (c n)) (hb : UB c)
    (hz : ∀ x, ∀ᶠ n in atTop, c n x = 0) {g : ℝ → ℝ} (hg : MemLp g 2 μ) :
    ZL μ (fun n x => c n x * g x) := by
  obtain ⟨K, hK⟩ := hb
  have hm : ∀ n, MemLp (fun x => c n x * g x) 2 μ := fun n =>
    hg.of_le_mul (c := K) ((hcont n).aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hK n x) (abs_nonneg _))
  refine ⟨hm, tendsto_toLp_zero hm ?_⟩
  have hg2 : Integrable (fun x => (g x) ^ 2) μ := hg.integrable_sq
  have := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun (n : ℕ) x => (c n x * g x) ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => K ^ 2 * (g x) ^ 2)
    (fun n => (((hcont n).aestronglyMeasurable.mul hg.aestronglyMeasurable).pow 2))
    (hg2.const_mul _)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_mul_of_nonneg_right (by nlinarith [hK n x, abs_nonneg (c n x), sq_abs (c n x)])
        (sq_nonneg _))
    (Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hz x] with n hn
      rw [hn]; simp)
  simpa using this

end ZL

/-! ### The cut-off coefficient families -/

lemma chiR_eventually_lt (x : ℝ) : ∀ᶠ n : ℕ in atTop, |x| < Rn n := by
  filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with n hn
  unfold Rn
  have := (Nat.le_ceil |x|).trans (by exact_mod_cast hn : (⌈|x|⌉₊ : ℝ) ≤ n)
  linarith

/-- `Good` coefficient families: continuous, uniformly bounded, eventually `0` at every point. -/
def Good (c : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, Continuous (c n)) ∧ UB c ∧ ∀ x, ∀ᶠ n in atTop, c n x = 0

lemma ZL.of_good {μ : Measure ℝ} {c : ℕ → ℝ → ℝ} (hc : Good c) {g : ℝ → ℝ} (hg : MemLp g 2 μ) :
    ZL μ (fun n x => c n x * g x) :=
  ZL.of_mul hc.1 hc.2.1 hc.2.2 hg

namespace GibbsData
variable (G : GibbsData)

/-- all the coefficient families of the cut-off commutators are `Good` (bounded jets of `V`). -/
theorem coeff_good (hb : G.BddJet) :
    Good (fun n x => chiR (Rn n) x - 1) ∧ Good (fun n x => Lg G.V (chiR (Rn n)) x) ∧
    Good (fun n x => 2 * deriv (chiR (Rn n)) x) ∧ Good (fun n x => cc0 G.V (chiR (Rn n)) x) ∧
    Good (fun n x => cc1 G.V (chiR (Rn n)) x) ∧ Good (fun n x => cc2 G.V (chiR (Rn n)) x) ∧
    Good (fun n x => cc3 (chiR (Rn n)) x) ∧ Good (fun n x => cc4 G.V (chiR (Rn n)) x) := by
  obtain ⟨⟨M1, hM1⟩, ⟨M2, hM2⟩, ⟨M3, hM3⟩⟩ := hb
  obtain ⟨K, hK1, hK⟩ := chiR_iter_bound
  -- atoms
  have a0 : UB (fun n x => chiR (Rn n) x) := ⟨K, fun n x => by simpa using hK 0 (by norm_num) n x⟩
  have a1 : UB (fun n x => deriv (chiR (Rn n)) x) := ⟨K, fun n x => by simpa using hK 1 (by norm_num) n x⟩
  have a2 : UB (fun n x => deriv (deriv (chiR (Rn n))) x) :=
    ⟨K, fun n x => by simpa using hK 2 (by norm_num) n x⟩
  have a3 : UB (fun n x => deriv (deriv (deriv (chiR (Rn n)))) x) :=
    ⟨K, fun n x => by simpa using hK 3 (by norm_num) n x⟩
  have a4 : UB (fun n x => deriv (deriv (deriv (deriv (chiR (Rn n))))) x) :=
    ⟨K, fun n x => by simpa using hK 4 (by norm_num) n x⟩
  have w1 : UB (fun (_ : ℕ) x => deriv G.V x) := ⟨M1, fun _ x => hM1 x⟩
  have w2 : UB (fun (_ : ℕ) x => deriv (deriv G.V) x) := ⟨M2, fun _ x => hM2 x⟩
  have w3 : UB (fun (_ : ℕ) x => deriv (deriv (deriv G.V)) x) := ⟨M3, fun _ x => hM3 x⟩
  -- continuity of atoms
  have ψs : ∀ n, Sm (chiR (Rn n)) := fun n => chiR_smooth _
  have c0 : ∀ n, Continuous (chiR (Rn n)) := fun n => (ψs n).continuous
  have c1 : ∀ n, Continuous (deriv (chiR (Rn n))) := fun n => (ψs n).deriv'.continuous
  have c2 : ∀ n, Continuous (deriv (deriv (chiR (Rn n)))) := fun n => (ψs n).deriv'.deriv'.continuous
  have c3 : ∀ n, Continuous (deriv (deriv (deriv (chiR (Rn n))))) :=
    fun n => (ψs n).deriv'.deriv'.deriv'.continuous
  have c4 : ∀ n, Continuous (deriv (deriv (deriv (deriv (chiR (Rn n)))))) :=
    fun n => (ψs n).deriv'.deriv'.deriv'.deriv'.continuous
  have v1 : Continuous (deriv G.V) := G.smooth.deriv'.continuous
  have v2 : Continuous (deriv (deriv G.V)) := G.smooth.deriv'.deriv'.continuous
  have v3 : Continuous (deriv (deriv (deriv G.V))) := G.smooth.deriv'.deriv'.deriv'.continuous
  -- vanishing
  have z : ∀ x, ∀ᶠ n in atTop, chiR (Rn n) x = 1 ∧ deriv (chiR (Rn n)) x = 0 ∧
      deriv (deriv (chiR (Rn n))) x = 0 ∧ deriv (deriv (deriv (chiR (Rn n)))) x = 0 ∧
      deriv (deriv (deriv (deriv (chiR (Rn n))))) x = 0 := by
    intro x
    filter_upwards [chiR_eventually_lt x] with n hn
    exact ⟨chiR_eq_one_of (Rn_pos n) hn.le, chiR_iter_zero hn 0, chiR_iter_zero hn 1,
      chiR_iter_zero hn 2, chiR_iter_zero hn 3⟩
  have one : UB (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) := UB.const 1
  have two : UB (fun (_ : ℕ) (_ : ℝ) => (2 : ℝ)) := UB.const 2
  have four : UB (fun (_ : ℕ) (_ : ℝ) => (4 : ℝ)) := UB.const 4
  have g1 : Good (fun n x => chiR (Rn n) x - 1) :=
    ⟨fun n => (c0 n).sub continuous_const, a0.sub one, fun x => by
      filter_upwards [z x] with n hn
      simp [hn.1]⟩
  have g2 : Good (fun n x => Lg G.V (chiR (Rn n)) x) :=
    ⟨fun n => by
      simp only [Lg]; exact (c2 n).sub (v1.mul (c1 n)),
     by simp only [Lg]; exact a2.sub (w1.mul a1), fun x => by
      filter_upwards [z x] with n hn
      simp [Lg, hn.2.1, hn.2.2.1]⟩
  have g3 : Good (fun n x => 2 * deriv (chiR (Rn n)) x) :=
    ⟨fun n => continuous_const.mul (c1 n), two.mul a1, fun x => by
      filter_upwards [z x] with n hn
      simp [hn.2.1]⟩
  have g4 : Good (fun n x => cc0 G.V (chiR (Rn n)) x) :=
    ⟨fun n => by
      have := c1 n; have := c2 n; have := c3 n; have := c4 n
      simp only [cc0]; fun_prop,
     by
      simp only [cc0]
      repeat (first | assumption | exact UB.const _ | apply UB.sub | apply UB.add | apply UB.mul),
     fun x => by
      filter_upwards [z x] with n hn
      simp [cc0, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2]⟩
  have g5 : Good (fun n x => cc1 G.V (chiR (Rn n)) x) :=
    ⟨fun n => by
      have := c1 n; have := c2 n; have := c3 n
      simp only [cc1]; fun_prop,
     by
      simp only [cc1]
      repeat (first | assumption | exact UB.const _ | apply UB.sub | apply UB.add | apply UB.mul),
     fun x => by
      filter_upwards [z x] with n hn
      simp [cc1, hn.2.1, hn.2.2.1, hn.2.2.2.1]⟩
  have g6 : Good (fun n x => cc2 G.V (chiR (Rn n)) x) :=
    ⟨fun n => by
      have := c1 n; have := c2 n
      simp only [cc2]; fun_prop,
     by
      simp only [cc2]
      repeat (first | assumption | exact UB.const _ | apply UB.sub | apply UB.add | apply UB.mul),
     fun x => by
      filter_upwards [z x] with n hn
      simp [cc2, hn.2.1, hn.2.2.1]⟩
  have g7 : Good (fun n x => cc3 (chiR (Rn n)) x) :=
    ⟨fun n => by
      have := c1 n
      simp only [cc3]; fun_prop,
     by
      simp only [cc3]
      repeat (first | assumption | exact UB.const _ | apply UB.sub | apply UB.add | apply UB.mul),
     fun x => by
      filter_upwards [z x] with n hn
      simp [cc3, hn.2.1]⟩
  have g8 : Good (fun n x => cc4 G.V (chiR (Rn n)) x) :=
    ⟨fun n => by
      have := c1 n; have := c2 n
      simp only [cc4, Lg]; fun_prop,
     by
      simp only [cc4, Lg]
      repeat (first | assumption | exact UB.const _ | apply UB.sub | apply UB.add | apply UB.mul),
     fun x => by
      filter_upwards [z x] with n hn
      simp [cc4, Lg, hn.2.1, hn.2.2.1]⟩
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩

/-- **The three graph-norm cut-off estimates**: `χ_n v → v`, `L(χ_n v) → L v`, `L²(χ_n v) → L² v` in `L²(μ)`. -/
theorem cutoff_ZL (hb : G.BddJet) {v : ℝ → ℝ} (hv : Sm v) (h0 : MemLp v 2 G.μ)
    (h1 : MemLp (deriv v) 2 G.μ) (h2 : MemLp (deriv (deriv v)) 2 G.μ)
    (h3 : MemLp (deriv (deriv (deriv v))) 2 G.μ) (hLv : MemLp (Lg G.V v) 2 G.μ)
    (hLLv : MemLp (Lg G.V (Lg G.V v)) 2 G.μ) :
    ZL G.μ (fun n x => chiR (Rn n) x * v x - v x) ∧
    ZL G.μ (fun n x => Lg G.V (chiR (Rn n) * v) x - Lg G.V v x) ∧
    ZL G.μ (fun n x => Lg G.V (Lg G.V (chiR (Rn n) * v)) x - Lg G.V (Lg G.V v) x) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := G.coeff_good hb
  refine ⟨?_, ?_, ?_⟩
  · exact (ZL.of_good g1 h0).congr (fun n x => by ring)
  · refine (((ZL.of_good g1 hLv).add (ZL.of_good g2 h0)).add (ZL.of_good g3 h1)).congr (fun n x => ?_)
    rw [L_mul_expand (chiR_smooth _) hv x]
  · refine (((((ZL.of_good g1 hLLv).add (ZL.of_good g4 h0)).add (ZL.of_good g5 h1)).add
      (ZL.of_good g6 h2)).add (ZL.of_good g7 h3)).add (ZL.of_good g8 hLv) |>.congr (fun n x => ?_)
    rw [LL_mul_expand G.smooth (chiR_smooth _) hv x]

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
