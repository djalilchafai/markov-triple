import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdDefs

/-!
# `GrowHess3`: the hypothesis of the weighted `ℝ^d` `Core2` theorem (R19, Stream A5, target C0)

Statements: `STATEMENTS_R19_Core2Rd.md` (C0).  `Hess V` and `∇³V` are controlled by `1 + Σ|∂ₖV|` (the `ℝ^d` analogue of the 1-D
`GrowHess`), instead of being bounded (`BddHess3`, R18).  The weight `∇V` may grow arbitrarily fast
(e.g. `V = Σ xᵢ⁴/4 + xᵢ²/2`).
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- `Σₖ |∂ₖV x|` -/
noncomputable def gradL1 (V : Rd d → ℝ) (x : Rd d) : ℝ := ∑ k, |pderiv V k x|

lemma gradL1_nonneg (V : Rd d → ℝ) (x : Rd d) : 0 ≤ gradL1 V x := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **C0**: `∂ᵢ∂ⱼV`, `∂ᵢ∂ⱼ∂ₖV` are dominated by `1 + Σ|∂ₗV|` (BGL has no such condition; it is what the cut-off argument uses). -/
structure GibbsRdData.GrowHess3 (G : GibbsRdData d) : Prop where
  hess : ∃ C : ℝ, ∀ (x : Rd d) (i j : Fin d), |pderiv (pderiv G.V i) j x| ≤ C * (1 + gradL1 G.V x)
  third : ∃ C : ℝ, ∀ (x : Rd d) (i j k : Fin d),
    |pderiv (pderiv (pderiv G.V i) j) k x| ≤ C * (1 + gradL1 G.V x)

/-- `BddHess3 ⇒ GrowHess3`. -/
theorem GibbsRdData.BddHess3.growHess3 {G : GibbsRdData d} (hb : G.BddHess3) : G.GrowHess3 := by
  obtain ⟨C2, h2⟩ := hb.hess
  obtain ⟨C3, h3⟩ := hb.third
  have key : ∀ (C : ℝ) (y : ℝ) (x : Rd d), |y| ≤ C → |y| ≤ max C 0 * (1 + gradL1 G.V x) := by
    intro C y x h
    have h1 : 1 ≤ 1 + gradL1 G.V x := by linarith [gradL1_nonneg G.V x]
    have h0 : 0 ≤ max C 0 := le_max_right _ _
    nlinarith [le_max_left C 0]
  exact ⟨⟨max C2 0, fun x i j => key C2 _ x (h2 x i j)⟩, ⟨max C3 0, fun x i j k => key C3 _ x (h3 x i j k)⟩⟩

/-- `Σ ∂ᵢ∂ᵢV ≤ |∇V|²/4 + B` (the Hardy hypothesis). -/
theorem GibbsRdData.GrowHess3.laplace_le {G : GibbsRdData d} (hg : G.GrowHess3) :
    ∃ B : ℝ, ∀ x : Rd d, ∑ i, pderiv (pderiv G.V i) i x ≤ (∑ k, pderiv G.V k x ^ 2) / 4 + B := by
  obtain ⟨C0, hC⟩ := hg.hess
  set C : ℝ := max C0 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨d * C + (d : ℝ) ^ 3 * C ^ 2, fun x => ?_⟩
  set s := gradL1 G.V x with hs
  set N := ∑ k, pderiv G.V k x ^ 2 with hN
  have hs0 : 0 ≤ s := gradL1_nonneg G.V x
  have hsum : ∑ i, pderiv (pderiv G.V i) i x ≤ d * (C * (1 + s)) := by
    have : ∑ i, pderiv (pderiv G.V i) i x ≤ ∑ _i : Fin d, C * (1 + s) :=
      Finset.sum_le_sum fun i _ => ((le_abs_self _).trans (hC x i i)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    simpa using this
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [hN] at hsum ⊢
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hcs : s ^ 2 ≤ d * N := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun k => |pderiv G.V k x|)
    simpa [hs, hN, gradL1, sq_abs] using this
  have h4 : 4 * d * (d * C * s) ≤ 4 * d * (N / 4 + (d : ℝ) ^ 3 * C ^ 2) := by
    nlinarith [sq_nonneg (s - 2 * (d : ℝ) ^ 2 * C)]
  have h5 : d * C * s ≤ N / 4 + (d : ℝ) ^ 3 * C ^ 2 :=
    le_of_mul_le_mul_left h4 (by positivity)
  nlinarith

/-- a coefficient dominated by `C(1+Σ|∂ₖV|)` times a function `g` with all `∂ₖV·g ∈ L²` is `L²` after multiplication by `g`. -/
lemma memLp_mul_growth {μ : Measure (Rd d)} {V c g : Rd d → ℝ} (hc : AEStronglyMeasurable c μ)
    {C : ℝ} (hC : ∀ x, |c x| ≤ C * (1 + gradL1 V x)) (hg : MemLp g 2 μ)
    (hVg : ∀ k, MemLp (fun x => pderiv V k x * g x) 2 μ) : MemLp (fun x => c x * g x) 2 μ := by
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have h1 : 0 < 1 + gradL1 V 0 := by linarith [gradL1_nonneg V 0]
    by_contra hneg
    have hneg' : C < 0 := not_le.1 hneg
    nlinarith [abs_nonneg (c 0), mul_neg_of_neg_of_pos hneg' h1]
  have hbd : MemLp (fun x => C * (|g x| + ∑ k, |pderiv V k x * g x|)) 2 μ := by
    have h := (hg.norm.add (memLp_finsetSum' Finset.univ fun k _ => (hVg k).norm)).const_mul C
    simpa [Finset.sum_apply] using h
  refine hbd.mono' (hc.mul hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have e : C * (|g x| + ∑ k, |pderiv V k x * g x|) = C * (1 + gradL1 V x) * |g x| := by
    simp only [gradL1, abs_mul]
    rw [← Finset.sum_mul]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

end MarkovTriple.BGL.Instances.GibbsRd
