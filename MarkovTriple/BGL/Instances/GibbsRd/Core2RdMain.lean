import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdAssemble
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdCut
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdEnergy
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdResolvent

/-!
# `Core2` and the unconditional converse of BGL Prop. 3.3.17 for Gibbs measures on `ℝ^d` (R18, Stream A3)

Statements: `STATEMENTS_R18_Core2Rd.md` (B5).  Hypothesis: `G.BddHess3` (bounded `Hess V` and `∇³V`; `∇V` may grow linearly,
so `Hess V ≥ ρ > 0` is allowed).  Proof: resolvent solution (`exists_resolvent_smooth`), `∇v, ∇²v ∈ L²` (cut-off Caccioppoli and
Bochner, `Core2RdEnergy`), cut-off commutators with uniform bounds (`Core2RdCut`) and dominated convergence
(`Core2RdCutZL`, `Core2RdAssemble`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.BGL (FullTriple DiffusionTriple pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

lemma eventually_qd_lt (x : Rd d) : ∀ᶠ n : ℕ in atTop, qd x < ((n : ℝ) + 1) ^ 2 := by
  filter_upwards [eventually_ge_atTop (⌈qd x⌉₊)] with n hn
  have h1 : qd x ≤ n := (Nat.le_ceil (qd x)).trans (by exact_mod_cast hn)
  have h2 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- bounded Hessian gives a (negative) lower Hessian bound `Hess V ≥ -d C`. -/
theorem BddHess3.hessGe {G : GibbsRdData d} (hb : G.BddHess3) : ∃ ρ : ℝ, HessGe G.V ρ := by
  obtain ⟨C, hC⟩ := hb.hess
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i0⟩⟩
  · exact ⟨0, fun x v => by simp⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 i0 i0)
  refine ⟨-(d * C), fun x v => ?_⟩
  have h1 : ∀ i j, pderiv (pderiv G.V i) j x * v i * v j ≥ -(C * (|v i| * |v j|)) := by
    intro i j
    have : |pderiv (pderiv G.V i) j x * v i * v j| ≤ C * (|v i| * |v j|) := by
      rw [abs_mul, abs_mul]
      have := mul_le_mul_of_nonneg_right (hC x i j) (mul_nonneg (abs_nonneg (v i)) (abs_nonneg (v j)))
      linarith
    have := neg_abs_le (pderiv (pderiv G.V i) j x * v i * v j)
    linarith
  have h2 : ∑ i, ∑ j, pderiv (pderiv G.V i) j x * v i * v j ≥ -(C * ∑ i, ∑ j, |v i| * |v j|) := by
    have : -(C * ∑ i, ∑ j, |v i| * |v j|) = ∑ i, ∑ j, -(C * (|v i| * |v j|)) := by
      simp only [Finset.sum_neg_distrib, Finset.mul_sum]
    rw [this]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
  have h3 : ∑ i, ∑ j, |v i| * |v j| = (∑ i, |v i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have h4 : (∑ i, |v i|) ^ 2 ≤ d * ∑ i, v i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun i => |v i|)
    simpa [sq_abs] using this
  rw [h3] at h2
  nlinarith [mul_le_mul_of_nonneg_left h4 hC0]

lemma coeffGood (hb : G.BddHess3) : CoeffGood G.V := by
  obtain ⟨K, hK⟩ := cut_bounds G hb
  obtain ⟨C2, hC2⟩ := hb.hess
  have hs : ∀ n : ℕ, Sm (chi n : Rd d → ℝ) := fun n => sm_cut _
  have hz : ∀ x : Rd d, ∀ᶠ n : ℕ in atTop, qd x < ((n : ℝ) + 1) ^ 2 := eventually_qd_lt
  -- the two index-free families
  have hLL : Good (fun (n : ℕ) (x : Rd d) => Lr G.V (chi n) x) ∧
      Good (fun (n : ℕ) (x : Rd d) => Lr G.V (Lr G.V (chi n)) x) := by
    rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i0⟩⟩
    · have h0 : ∀ f : Rd d → ℝ, ∀ x, Lr G.V f x = 0 := fun f x => by simp [Lr]
      refine ⟨⟨fun n => (sm_Lr G.smooth (hs n)).continuous, ⟨0, fun n x => ?_⟩, fun x => ?_⟩,
        ⟨fun n => (sm_Lr G.smooth (sm_Lr G.smooth (hs n))).continuous, ⟨0, fun n x => ?_⟩, fun x => ?_⟩⟩
      all_goals (simp only [h0]; simp)
    · refine ⟨⟨fun n => (sm_Lr G.smooth (hs n)).continuous, ⟨K, fun n x => (hK n x i0 i0).2.2.2.1⟩,
        fun x => ?_⟩, ⟨fun n => (sm_Lr G.smooth (sm_Lr G.smooth (hs n))).continuous,
        ⟨K, fun n x => (hK n x i0 i0).2.2.2.2.2⟩, fun x => ?_⟩⟩
      · filter_upwards [hz x] with n hn
        exact (cut_vanish G n hn i0 i0).2.2.1
      · filter_upwards [hz x] with n hn
        exact (cut_vanish G n hn i0 i0).2.2.2.2
  refine ⟨⟨fun n => ((hs n).continuous.sub continuous_const), ⟨1, fun n x => ?_⟩, fun x => ?_⟩,
    hLL.1,
    fun i => ⟨fun n => ((hs n).pderiv i).continuous, ⟨K, fun n x => ?_⟩, fun x => ?_⟩,
    fun i j => ⟨fun n => (((hs n).pderiv i).pderiv j).continuous, ⟨K, fun n x => ?_⟩, fun x => ?_⟩,
    fun i => ⟨fun n => ((sm_Lr G.smooth (hs n)).pderiv i).continuous, ⟨K, fun n x => ?_⟩, fun x => ?_⟩,
    hLL.2,
    fun i j => ⟨fun n => (((G.smooth.pderiv i).pderiv j).mul ((hs n).pderiv i)).continuous,
      ⟨C2 * K, fun n x => ?_⟩, fun x => ?_⟩⟩
  · have h0 := cut_nonneg (((n : ℕ) : ℝ) + 1) x
    have h1 := cut_le_one (((n : ℕ) : ℝ) + 1) x
    show |cut _ x - 1| ≤ 1
    rw [abs_le]; constructor <;> linarith
  · filter_upwards [hz x] with n hn
    have : cut (((n : ℕ) : ℝ) + 1) x = 1 := cut_eq_one (by positivity) (le_of_lt hn)
    show cut _ x - 1 = 0
    rw [this]; ring
  · exact (hK n x i i).2.1
  · filter_upwards [hz x] with n hn
    exact (cut_vanish G n hn i i).1
  · exact (hK n x i j).2.2.1
  · filter_upwards [hz x] with n hn
    exact (cut_vanish G n hn i j).2.1
  · exact (hK n x i i).2.2.2.2.1
  · filter_upwards [hz x] with n hn
    exact (cut_vanish G n hn i i).2.2.2.1
  · have h1 := (hK n x i j).2.1
    have h2 := hC2 x i j
    show |pderiv (pderiv G.V i) j x * pderiv (cut ((n : ℝ) + 1)) i x| ≤ C2 * K
    rw [abs_mul]
    exact mul_le_mul h2 h1 (abs_nonneg _) ((abs_nonneg _).trans h2)
  · filter_upwards [hz x] with n hn
    show pderiv (pderiv G.V i) j x * pderiv (cut ((n : ℝ) + 1)) i x = 0
    rw [(cut_vanish G n hn i j).1]; ring

/-- **B5: `Core2` for the Gibbs Full Markov triple on `ℝ^d`** with bounded `Hess V`, `∇³V` (and nothing else). -/
theorem gibbsRd_core2 (hb : G.BddHess3) : G.gibbsRdFull_unconditional.Core2 := by
  intro a
  have ha : a.1 ∈ A₀ d := a.2
  obtain ⟨v, hv, hv2, hL⟩ := G.exists_resolvent_smooth ha
  obtain ⟨ρ, hρ⟩ := BddHess3.hessGe hb
  obtain ⟨K, hK⟩ := cut_bounds G hb
  have hP : ∃ K : ℝ, ∀ (n : ℕ) x, |Lr G.V (cut ((n : ℝ) + 1)) x| ≤ K := by
    by_cases hne : Nonempty (Fin d)
    · obtain ⟨i0⟩ := hne
      exact ⟨K, fun n x => (hK n x i0 i0).2.2.2.1⟩
    · have h0 : ∀ f : Rd d → ℝ, ∀ x, Lr G.V f x = 0 := fun f x => by
        have : IsEmpty (Fin d) := not_nonempty_iff.1 hne
        simp [Lr]
      exact ⟨0, fun n x => by simp [h0]⟩
  have h1 := fun i => G.memLp_grad_resolvent hv ha hv2 hL i
  have h2 := fun i j => G.memLp_hess_resolvent hv ha hv2 hL hρ hP i j
  have haL : MemLp a.1 2 G.toEll.μ := ha.1.continuous.memLp_of_hasCompactSupport ha.2
  have hLvf : Lr G.V v = fun x => v x - a.1 x := funext hL
  have hLa : Lr G.V a.1 ∈ A₀ d := by
    have := G.toEll.L_mem ha
    rwa [G.toEll_L ha.1] at this
  have hLaL : MemLp (Lr G.V a.1) 2 G.toEll.μ := hLa.1.continuous.memLp_of_hasCompactSupport hLa.2
  have hLv : MemLp (Lr G.V v) 2 G.toEll.μ := by rw [hLvf]; exact hv2.sub haL
  have hLLvf : Lr G.V (Lr G.V v) = fun x => (v x - a.1 x) - Lr G.V a.1 x := by
    funext x
    have e : Lr G.V v = fun y => v y + (-1 : ℝ) * a.1 y := by rw [hLvf]; funext y; ring
    rw [e, Lr_add_smul hv ha.1 (-1) x, hL x]; ring
  have hLLv : MemLp (Lr G.V (Lr G.V v)) 2 G.toEll.μ := by
    rw [hLLvf]; exact (hv2.sub haL).sub hLaL
  have hLv1 : ∀ i, MemLp (pderiv (Lr G.V v) i) 2 G.toEll.μ := fun i => by
    have e : pderiv (Lr G.V v) i = fun x => pderiv v i x - pderiv a.1 i x := by
      funext x
      rw [hLvf]
      exact pderiv_sub' hv ha.1 i x
    rw [e]
    exact (h1 i).sub ((A₀.pderiv_mem ha i).1.continuous.memLp_of_hasCompactSupport (A₀.pderiv_mem ha i).2)
  exact G.core2_of_ZL hv hL (cutoff_ZL G.smooth (G.coeffGood hb) hv hv2 h1 h2 hLv hLLv hLv1)

/-- **B5: the converse of BGL Prop. 3.3.17 (p. 162), unconditional for Gibbs triples on `ℝ^d` with `BddHess3`**:
`f ∈ 𝒜 ∩ L²(μ)` with `Γ(f), Γ₂(f) ∈ L¹(μ)` and `Hess V ≥ ρ` (any `ρ ∈ ℝ`) imply `[f] ∈ 𝒟(L)`, `L[f] = [Lf]` a.e. -/
theorem gibbsRd_mem_domain_of_Γ₂ (hb : G.BddHess3) {ρ : ℝ} (hρ : HessGe G.V ρ) {f : Rd d → ℝ}
    (hf : f ∈ G.gibbsRdFull_unconditional.A) (hf2 : MemLp f 2 G.toEll.μ)
    (hG : Integrable (FullTriple.G G.gibbsRdFull_unconditional f f) G.toEll.μ)
    (hG2 : Integrable (G.gibbsRdFull_unconditional.toDiffusionTriple.Γ₂ f f) G.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ G.gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      ((G.gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 G.toEll.μ) :
        Rd d → ℝ) =ᵐ[G.toEll.μ] G.gibbsRdFull_unconditional.L f :=
  FullTriple.mem_domain_of_Γ₂ (G.gibbsRdFull_CD_unconditional hρ) (G.gibbsRd_core2 hb) hf hf2 hG hG2

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
