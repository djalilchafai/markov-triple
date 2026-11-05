import Mathlib
import MarkovTriple.Stochastic.R30T.Approx
import MarkovTriple.Stochastic.R29.Conditional

/-!
# Round 30 (T), part 2: continuous bounded representatives of `P_t f`, `f ∈ C_c`, on `ℝ^d`  (G1, G2)

For `S : FullTriple (ℝ^d)` with `S.A = C^∞` (field F8 `semigroup_A`) and `S.A₀ = C_c^∞`, `P_t [h]` has a smooth representative for `h ∈ C_c^∞`.
Sup-norm approximation (`Approx.lean`) and the sub-Markov bound give a continuous representative with `|g| ≤ ‖f‖_∞` for every `f ∈ C_c`.
No curvature or ellipticity is used.  See `STATEMENTS_R30_T.md`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R30T

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24

section Generic

variable {d : ℕ} (S : FullTriple (Rd d)) [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ]
  [S.toDiffusionTriple.μ.IsOpenPosMeasure]

omit [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ] in
/-- an a.e. inequality between continuous functions holds everywhere (full support) -/
lemma le_of_ae_le_cont {u v : Rd d → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : u ≤ᵐ[S.toDiffusionTriple.μ] v) (x : Rd d) : u x ≤ v x := by
  by_contra hx
  rw [not_le] at hx
  have ho : IsOpen {y | v y < u y} := isOpen_lt hv hu
  have h0 : S.toDiffusionTriple.μ {y | v y < u y} = 0 := by
    have := ae_iff.1 h
    simpa [not_le] using this
  exact (ho.measure_pos S.toDiffusionTriple.μ ⟨x, hx⟩).ne' h0

variable (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d)
include hA hA₀

omit [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ] [S.toDiffusionTriple.μ.IsOpenPosMeasure] in
/-- for `h ∈ C_c^∞`, `P_t [h]` has a continuous (indeed smooth) representative -/
lemma cont_rep_A₀ (t : ℝ≥0) (h : Rd d → ℝ) (hh : h ∈ A₀ d) :
    ∃ g : Rd d → ℝ, Continuous g ∧
      (S.toDiffusionTriple.semigroup t (S.toDiffusionTriple.cls ⟨h, hA₀ ▸ hh⟩) : Rd d → ℝ)
        =ᵐ[S.toDiffusionTriple.μ] g := by
  refine ⟨S.Pt t ⟨h, hA₀ ▸ hh⟩, ?_, S.Pt_ae t _⟩
  have := S.Pt_mem_A t ⟨h, hA₀ ▸ hh⟩
  rw [hA] at this
  exact (mem_Afull.1 this).continuous

theorem rd_semigroup_cc_exists_cont (t : ℝ≥0)
    (f : C_c(Rd d, ℝ)) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∃ g : C(Rd d, ℝ), (∀ x, |g x| ≤ C) ∧
      (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[S.toDiffusionTriple.μ] g := by
  set D := S.toDiffusionTriple with hD
  set P : Lp ℝ 2 D.μ := D.semigroup t (ccL2 D f) with hP
  -- approximants
  have hex : ∀ n : ℕ, ∃ h ∈ A₀ d, ∀ x, |h x - f x| < 1 / ((n : ℝ) + 1) := fun n =>
    exists_A₀_approx f (by positivity)
  choose h hhA hhf using hex
  have hrep : ∀ n, ∃ g : Rd d → ℝ, Continuous g ∧
      (D.semigroup t (D.cls ⟨h n, hA₀ ▸ hhA n⟩) : Rd d → ℝ) =ᵐ[D.μ] g := fun n =>
    cont_rep_A₀ S hA hA₀ t (h n) (hhA n)
  choose g hgc hgae using hrep
  -- a.e. closeness of `P` to `g n`
  have hclose : ∀ n : ℕ, ∀ᵐ x ∂D.μ, |(P : Rd d → ℝ) x - g n x| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    set u : Lp ℝ 2 D.μ := D.cls ⟨h n, hA₀ ▸ hhA n⟩ with hu
    have hu_ae : (u : Rd d → ℝ) =ᵐ[D.μ] h n := DiffusionTriple.coeFn_cls D _
    have h1 : ((ccL2 D f - u : Lp ℝ 2 D.μ) : Rd d → ℝ) ≤ᵐ[D.μ] fun _ => 1 / ((n : ℝ) + 1) := by
      filter_upwards [Lp.coeFn_sub (ccL2 D f) u, coeFn_ccL2 (T := D) f, hu_ae] with x a b c
      rw [a]; simp only [Pi.sub_apply, b, c]
      have := hhf n x
      rw [abs_lt] at this
      linarith
    have h2 : ((u - ccL2 D f : Lp ℝ 2 D.μ) : Rd d → ℝ) ≤ᵐ[D.μ] fun _ => 1 / ((n : ℝ) + 1) := by
      filter_upwards [Lp.coeFn_sub u (ccL2 D f), coeFn_ccL2 (T := D) f, hu_ae] with x a b c
      rw [a]; simp only [Pi.sub_apply, b, c]
      have := hhf n x
      rw [abs_lt] at this
      linarith
    have s1 := semigroup_le_const (T := D) t _ hε h1
    have s2 := semigroup_le_const (T := D) t _ hε h2
    have e1 : D.semigroup t (ccL2 D f - u) = D.semigroup t (ccL2 D f) - D.semigroup t u :=
      (D.semigroup t).map_sub _ _
    have e2 : D.semigroup t (u - ccL2 D f) = D.semigroup t u - D.semigroup t (ccL2 D f) :=
      (D.semigroup t).map_sub _ _
    rw [e1] at s1; rw [e2] at s2
    filter_upwards [s1, s2, Lp.coeFn_sub (D.semigroup t (ccL2 D f)) (D.semigroup t u),
      Lp.coeFn_sub (D.semigroup t u) (D.semigroup t (ccL2 D f)), hgae n] with x a b c d' e
    simp only [Pi.sub_apply] at a b c d'
    rw [c] at a; rw [d'] at b
    rw [abs_le]; rw [← e]
    constructor <;> linarith
  -- everywhere closeness of the continuous approximants
  have hgg : ∀ n m : ℕ, ∀ x, |g n x - g m x| ≤ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
    intro n m x
    have hae : ∀ᵐ y ∂D.μ, |g n y - g m y| ≤ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
      filter_upwards [hclose n, hclose m] with y a b
      rw [abs_le] at a b ⊢
      constructor <;> linarith [a.1, a.2, b.1, b.2]
    have := le_of_ae_le_cont S (u := fun y => |g n y - g m y|) (v := fun _ => 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1))
      (((hgc n).sub (hgc m)).abs) continuous_const hae x
    exact this
  -- the limit
  have hconv : ∀ x, ∃ y, Tendsto (fun n => g n x) atTop (𝓝 y) := by
    intro x
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hgg n N x) ?_
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    linarith
  choose gl hgl using hconv
  have hgl_bd : ∀ n x, |g n x - gl x| ≤ 1 / ((n : ℝ) + 1) := by
    intro n x
    have hlim : Tendsto (fun m => |g n x - g m x|) atTop (𝓝 |g n x - gl x|) :=
      ((tendsto_const_nhds.sub (hgl x)).abs)
    have hlim2 : Tendsto (fun m : ℕ => 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) atTop
        (𝓝 (1 / ((n : ℝ) + 1) + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have := le_of_tendsto_of_tendsto hlim hlim2 (Eventually.of_forall fun m => hgg n m x)
    simpa using this
  have hunif : TendstoUniformly g gl atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    refine lt_of_le_of_lt (hgl_bd n x) (lt_of_le_of_lt ?_ hN)
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hglc : Continuous gl := hunif.continuous (Eventually.of_forall hgc).frequently
  -- `P = gl` a.e.
  have hPg : (P : Rd d → ℝ) =ᵐ[D.μ] gl := by
    have hall : ∀ᵐ x ∂D.μ, ∀ n : ℕ, |(P : Rd d → ℝ) x - g n x| ≤ 1 / ((n : ℝ) + 1) :=
      ae_all_iff.2 hclose
    filter_upwards [hall] with x hx
    have hle : ∀ n : ℕ, |(P : Rd d → ℝ) x - gl x| ≤ 2 / ((n : ℝ) + 1) := by
      intro n
      calc |(P : Rd d → ℝ) x - gl x| = |((P : Rd d → ℝ) x - g n x) + (g n x - gl x)| := by ring_nf
        _ ≤ |(P : Rd d → ℝ) x - g n x| + |g n x - gl x| := abs_add_le _ _
        _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_le_add (hx n) (hgl_bd n x)
        _ = 2 / ((n : ℝ) + 1) := by ring
    have h0 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
      simpa [div_eq_mul_inv] using this
    have : |(P : Rd d → ℝ) x - gl x| ≤ 0 :=
      ge_of_tendsto' h0 hle
    have := abs_nonneg ((P : Rd d → ℝ) x - gl x)
    have h3 : |(P : Rd d → ℝ) x - gl x| = 0 := le_antisymm ‹_› this
    exact sub_eq_zero.1 (abs_eq_zero.1 h3)
  -- the bound
  have hbd : ∀ x, |gl x| ≤ C := by
    intro x
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hpos : 0 < C + δ := by linarith
    have h1 : ((ccL2 D f : Lp ℝ 2 D.μ) : Rd d → ℝ) ≤ᵐ[D.μ] fun _ => C + δ := by
      filter_upwards [coeFn_ccL2 (T := D) f] with y hy
      rw [hy]; exact (le_abs_self _).trans ((hC y).trans (by linarith))
    have h2 : ((-ccL2 D f : Lp ℝ 2 D.μ) : Rd d → ℝ) ≤ᵐ[D.μ] fun _ => C + δ := by
      filter_upwards [Lp.coeFn_neg (ccL2 D f), coeFn_ccL2 (T := D) f] with y a hy
      rw [a]; simp only [Pi.neg_apply, hy]
      exact (neg_le_abs _).trans ((hC y).trans (by linarith))
    have s1 := semigroup_le_const (T := D) t _ hpos h1
    have s2 := semigroup_le_const (T := D) t _ hpos h2
    have e2 : D.semigroup t (-ccL2 D f) = -D.semigroup t (ccL2 D f) := (D.semigroup t).map_neg _
    rw [e2] at s2
    have hae : |gl| ≤ᵐ[D.μ] fun _ => C + δ := by
      filter_upwards [s1, s2, Lp.coeFn_neg (D.semigroup t (ccL2 D f)), hPg] with y a b c e
      simp only [Pi.neg_apply] at b c
      have b' : -(P : Rd d → ℝ) y ≤ C + δ := by
        have : (-(D.semigroup t (ccL2 D f)) : Lp ℝ 2 D.μ) y = -(P : Rd d → ℝ) y := by
          simpa using c
        rw [this] at b; exact b
      have a' : (P : Rd d → ℝ) y ≤ C + δ := a
      show |gl y| ≤ C + δ
      rw [← e]; exact abs_le.2 ⟨by linarith, a'⟩
    have := le_of_ae_le_cont S (u := fun y => |gl y|) (v := fun _ => C + δ) hglc.abs continuous_const hae x
    exact this
  exact ⟨⟨gl, hglc⟩, hbd, hPg⟩

theorem rd_isFellerC0_iff_decay :
    IsFellerC0 S.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (f : C_c(Rd d, ℝ)) (g : C(Rd d, ℝ)),
      (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[S.toDiffusionTriple.μ] g → Tendsto g (cocompact (Rd d)) (𝓝 0) := by
  constructor
  · intro hF t f g hg
    obtain ⟨g', hg'⟩ := hF t f (ccL2 S.toDiffusionTriple f) (coeFn_ccL2 (T := S.toDiffusionTriple) f)
    have hgg : ∀ x, g x = g' x := by
      have h1 : (g : Rd d → ℝ) =ᵐ[S.toDiffusionTriple.μ] g' := hg.symm.trans hg'
      intro x
      exact le_antisymm (le_of_ae_le_cont S g.continuous g'.continuous h1.le x)
        (le_of_ae_le_cont S g'.continuous g.continuous h1.symm.le x)
    have : (g : Rd d → ℝ) = g' := funext hgg
    rw [this]
    exact g'.zero_at_infty'
  · intro hdec t f u hu
    have hC : ∃ C, ∀ y, |f y| ≤ C := by
      obtain ⟨C, hC⟩ := f.continuous.norm.bddAbove_range_of_hasCompactSupport
        (by simpa using f.hasCompactSupport.norm)
      exact ⟨C, fun y => hC ⟨y, rfl⟩⟩
    obtain ⟨C, hC⟩ := hC
    obtain ⟨g, -, hg⟩ := rd_semigroup_cc_exists_cont S hA hA₀ t f hC
    have hu' : u = ccL2 S.toDiffusionTriple f :=
      Lp.ext (hu.trans (coeFn_ccL2 (T := S.toDiffusionTriple) f).symm)
    subst hu'
    exact ⟨⟨g, hdec t f g hg⟩, hg⟩

end Generic

end MarkovTriple.Stochastic.R30T
