import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.DirectMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWExample
import MarkovTriple.BGL.Instances.Gibbs.DirectExample

/-!
# Non-vacuity of the direct converse on `ℝ^d`: a spiky separable potential outside `GrowHess3` (R20, Stream D1)

Statements: `Instances/Gibbs/STATEMENTS_R20_Direct.md` (D1-5).

## DIFFERENCE FROM BGL

BGL's converse of Prop. 3.3.17 needs the core of `L²` (`Core2`); the R18-R19 proofs of `Core2` on `ℝ^d` need `GrowHess3`
(`|∂²V|, |∂³V| ≤ C(1 + Σ|∂ₗV|)`).  The direct route (`gibbsRd_mem_domain_of_Γ₂_direct`) needs only `HessGe V ρ`.  The separable potential
`V(x) = Σᵢ v(xᵢ)` with `v'' = 2 + sin(e^{t²})` (`Gibbs/DirectExample`) has `Hess V ≥ I` (`ρ = 1 > 0`) and is NOT `GrowHess3`
(hence not `BddHess3`): `∂ᵢ³V` has superpolynomial peaks while `Σ|∂ₗV| ≤ 3 Σ|xₗ|` there.
-/

open MeasureTheory
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv FullTriple)
open MarkovTriple.BGL.Instances.Gibbs (spkV spkP1 spk sm_spkV sm_spkP1 sm_spk deriv_spkV deriv_spkP1 spk_ge spk_le
  spk_peak abs_spkP1_le)

variable {d : ℕ}

/-- `V(x) = Σᵢ v(xᵢ)`, `v = spkV`. -/
noncomputable def spkVd (d : ℕ) : Rd d → ℝ := fun x => ∑ i, spkV (x i)

lemma sm_spkVd (d : ℕ) : Sm (spkVd d) :=
  ContDiff.sum fun i _ => sm_fun_coord spkV sm_spkV i

lemma pderiv_spkVd (j : Fin d) (x : Rd d) : pderiv (spkVd d) j x = spkP1 (x j) := by
  unfold spkVd
  rw [pderiv_sum _ (fun i => sm_fun_coord spkV sm_spkV i) j x]
  have : ∀ i, pderiv (fun y : Rd d => spkV (y i)) j x = if j = i then spkP1 (x i) else 0 := by
    intro i
    refine (pderiv_fun_coord spkV (sm_spkV.differentiable (by simp)) i j x).trans ?_
    rw [deriv_spkV]
  simp only [this]
  simp

lemma pderiv_spkVd_fun (j : Fin d) : pderiv (spkVd d) j = fun y => spkP1 (y j) :=
  funext (pderiv_spkVd j)

lemma pderiv2_spkVd (i j : Fin d) (x : Rd d) :
    pderiv (pderiv (spkVd d) i) j x = if j = i then spk (x i) else 0 := by
  rw [pderiv_spkVd_fun i]
  refine (pderiv_fun_coord spkP1 (sm_spkP1.differentiable (by simp)) i j x).trans ?_
  rw [deriv_spkP1]

lemma pderiv3_spkVd (i j k : Fin d) (x : Rd d) :
    pderiv (pderiv (pderiv (spkVd d) i) j) k x = if j = i ∧ k = i then deriv spk (x i) else 0 := by
  have e : pderiv (pderiv (spkVd d) i) j = fun y => if j = i then spk (y i) else 0 :=
    funext (pderiv2_spkVd i j)
  rw [e]
  by_cases hj : j = i
  · simp only [hj, ite_true, true_and]
    exact pderiv_fun_coord spk (sm_spk.differentiable (by simp)) i k x
  · simp only [hj, ite_false, false_and]
    exact pderiv_const 0 k x

lemma hessGe_spkVd (d : ℕ) : HessGe (spkVd d) 1 := by
  intro x v
  simp only [pderiv2_spkVd, ite_mul, zero_mul]
  have e1 : ∀ i : Fin d, ∑ j, (if j = i then spk (x i) * v i * v j else 0) =
      spk (x i) * v i * v i := fun i => by simp
  simp only [e1]
  rw [one_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [mul_nonneg (sub_nonneg.2 (spk_ge (x i))) (sq_nonneg (v i))]

/-- the spiky separable Gibbs data on `ℝ^d` (`Hess V ≥ I`, `e^{-V}` integrable by `ofConvex`). -/
noncomputable def spikyData (d : ℕ) : GibbsRdData d :=
  GibbsRdData.ofConvex (sm_spkVd d) (by norm_num : (0 : ℝ) < 1) (hessGe_spkVd d)

lemma spikyData_V (d : ℕ) : (spikyData d).V = spkVd d := rfl

/-- **`GrowHess3` fails** for `d ≥ 1` (so also `BddHess3`). -/
theorem spikyData_not_growHess3 (d : ℕ) : ¬ (spikyData (d + 1)).GrowHess3 := by
  rintro ⟨-, C, hC⟩
  obtain ⟨x0, hx0X, hx01, hpk⟩ := spk_peak (max 1 (|C| + 1))
  have hC0 : |C| + 1 ≤ x0 := (le_max_right _ _).trans hx0X
  set x : Rd (d + 1) := fun i => if i = 0 then x0 else 0 with hx
  have hb := hC x 0 0 0
  change |pderiv (pderiv (pderiv (spkVd (d + 1)) 0) 0) 0 x| ≤ C * (1 + gradL1 (spkVd (d + 1)) x) at hb
  rw [pderiv3_spkVd] at hb
  simp only [and_self, ite_true, hx] at hb
  rw [hpk] at hb
  have hg : gradL1 (spkVd (d + 1)) x ≤ 3 * x0 := by
    unfold gradL1
    have : ∀ k : Fin (d + 1), |pderiv (spkVd (d + 1)) k x| = if k = 0 then |spkP1 x0| else 0 := by
      intro k
      rw [pderiv_spkVd]
      by_cases hk : k = 0
      · simp [hx, hk]
      · have : spkP1 0 = 0 := by simp [spkP1, MarkovTriple.BGL.Instances.Gibbs.prim]
        simp [hx, hk, this]
    simp only [this]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have := abs_spkP1_le x0
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x0)] at this
  have hC1 : C * (1 + gradL1 (spkVd (d + 1)) x) ≤ |C| * (1 + 3 * x0) := by
    have h1 : 0 ≤ gradL1 (spkVd (d + 1)) x := gradL1_nonneg _ _
    calc C * (1 + gradL1 (spkVd (d + 1)) x) ≤ |C| * (1 + gradL1 (spkVd (d + 1)) x) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      _ ≤ |C| * (1 + 3 * x0) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
  have hE : 1 + x0 ^ 2 ≤ Real.exp (x0 ^ 2) := by
    have := Real.add_one_le_exp (x0 ^ 2); linarith
  rw [abs_of_nonneg (by positivity)] at hb
  have hCa : 0 ≤ |C| := abs_nonneg C
  nlinarith [mul_le_mul_of_nonneg_right hE (by linarith : (0 : ℝ) ≤ 2 * x0), hb.trans hC1,
    mul_nonneg hCa (by linarith : (0 : ℝ) ≤ x0)]

/-- non-vacuity: `Hess V ≥ I`, NOT `GrowHess3`. -/
theorem spikyData_witness (d : ℕ) : HessGe (spikyData (d + 1)).V 1 ∧ ¬ (spikyData (d + 1)).GrowHess3 :=
  ⟨hessGe_spkVd (d + 1), spikyData_not_growHess3 d⟩

/-- the converse of BGL Prop. 3.3.17 for the spiky potential on `ℝ^d` (`ρ = 1`), outside `GrowHess3`/`BddHess3`. -/
theorem spikyData_mem_domain_of_Γ₂ (d : ℕ) {f : Rd d → ℝ}
    (hf : f ∈ (spikyData d).gibbsRdFull_unconditional.A) (hf2 : MemLp f 2 (spikyData d).toEll.μ)
    (hG : Integrable (FullTriple.G (spikyData d).gibbsRdFull_unconditional f f) (spikyData d).toEll.μ)
    (hG2 : Integrable ((spikyData d).gibbsRdFull_unconditional.toDiffusionTriple.Γ₂ f f)
      (spikyData d).toEll.μ) :
    ∃ hF : hf2.toLp f ∈ (spikyData d).gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      (((spikyData d).gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 (spikyData d).toEll.μ) : Rd d → ℝ) =ᵐ[(spikyData d).toEll.μ]
        (spikyData d).gibbsRdFull_unconditional.L f :=
  (spikyData d).gibbsRd_mem_domain_of_Γ₂_direct (hessGe_spkVd d) hf hf2 hG hG2

end MarkovTriple.BGL.Instances.GibbsRd
