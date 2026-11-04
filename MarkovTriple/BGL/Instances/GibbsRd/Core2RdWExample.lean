import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdExample

/-!
# Non-vacuity of the weighted `ℝ^d` `Core2` theorem: a `ρ > 0` potential OUTSIDE `BddHess3` (R19, Stream A5, target C6)

`quarV d (x) = Σᵢ (xᵢ⁴/4 + xᵢ²/2)` on `ℝ^d` (separable quartic): `∂ᵢ∂ⱼV = δᵢⱼ (3xᵢ² + 1)`, `∂ᵢ∂ⱼ∂ₖV = 6 xᵢ δᵢⱼ δᵢₖ`,
`∂ᵢV = xᵢ³ + xᵢ`.  `Hess V ≥ I` (`ρ = 1`), `GrowHess3` (constants `3`, `6`), and NOT `BddHess3` (for `d ≥ 1`).
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv FullTriple)

variable {d : ℕ}

/-- `∂ⱼ (g ∘ eval_i) = δ_{ji} g'(x_i)`. -/
lemma pderiv_fun_coord (g : ℝ → ℝ) (hg : Differentiable ℝ g) (i j : Fin d) (x : Rd d) :
    pderiv (fun y : Rd d => g (y i)) j x = if j = i then deriv g (x i) else 0 := by
  have h1 : HasFDerivAt (fun y : Rd d => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := hasFDerivAt_apply i x
  have h2 := (hg (x i)).hasDerivAt.comp_hasFDerivAt x h1
  unfold pderiv
  rw [show (fun y : Rd d => g (y i)) = g ∘ fun y : Rd d => y i from rfl, h2.fderiv]
  by_cases hj : j = i <;> simp [hj]

lemma sm_fun_coord (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) : Sm (fun y : Rd d => g (y i)) :=
  hg.comp (contDiff_apply ℝ ℝ i)

/-- the separable quartic potential. -/
noncomputable def quarV (d : ℕ) : Rd d → ℝ := fun x => ∑ i, (x i ^ 4 / 4 + x i ^ 2 / 2)

lemma sm_quarV (d : ℕ) : Sm (quarV d) :=
  ContDiff.sum fun i _ => sm_fun_coord (fun t => t ^ 4 / 4 + t ^ 2 / 2) (by fun_prop) i

lemma pderiv_quarV (j : Fin d) (x : Rd d) : pderiv (quarV d) j x = x j ^ 3 + x j := by
  unfold quarV
  rw [pderiv_sum _ (fun i => sm_fun_coord (fun t => t ^ 4 / 4 + t ^ 2 / 2) (by fun_prop) i) j x]
  have : ∀ i, pderiv (fun y : Rd d => y i ^ 4 / 4 + y i ^ 2 / 2) j x = if j = i then x i ^ 3 + x i else 0 := by
    intro i
    refine (pderiv_fun_coord (fun t : ℝ => t ^ 4 / 4 + t ^ 2 / 2) (by fun_prop) i j x).trans ?_
    have hd : deriv (fun t : ℝ => t ^ 4 / 4 + t ^ 2 / 2) (x i) = x i ^ 3 + x i := by
      have : HasDerivAt (fun t : ℝ => t ^ 4 / 4 + t ^ 2 / 2) (x i ^ 3 + x i) (x i) := by
        have := ((hasDerivAt_pow 4 (x i)).div_const 4).add ((hasDerivAt_pow 2 (x i)).div_const 2)
        convert this using 1
        ring
      exact this.deriv
    rw [hd]
  simp only [this]
  simp

lemma pderiv_quarV_fun (j : Fin d) : pderiv (quarV d) j = fun y => y j ^ 3 + y j :=
  funext (pderiv_quarV j)

lemma pderiv2_quarV (i j : Fin d) (x : Rd d) :
    pderiv (pderiv (quarV d) i) j x = if j = i then 3 * x i ^ 2 + 1 else 0 := by
  rw [pderiv_quarV_fun i]
  refine (pderiv_fun_coord (fun t : ℝ => t ^ 3 + t) (by fun_prop) i j x).trans ?_
  have : deriv (fun t : ℝ => t ^ 3 + t) (x i) = 3 * x i ^ 2 + 1 := by
    have : HasDerivAt (fun t : ℝ => t ^ 3 + t) (3 * x i ^ 2 + 1) (x i) := by
      have := (hasDerivAt_pow 3 (x i)).add (hasDerivAt_id (x i))
      convert this using 1
      rfl
    exact this.deriv
  rw [this]

lemma pderiv3_quarV (i j k : Fin d) (x : Rd d) :
    pderiv (pderiv (pderiv (quarV d) i) j) k x = if j = i ∧ k = i then 6 * x i else 0 := by
  have e : pderiv (pderiv (quarV d) i) j = fun y => if j = i then 3 * y i ^ 2 + 1 else 0 :=
    funext (pderiv2_quarV i j)
  rw [e]
  by_cases hj : j = i
  · simp only [hj, ite_true, true_and]
    refine (pderiv_fun_coord (fun t : ℝ => 3 * t ^ 2 + 1) (by fun_prop) i k x).trans ?_
    have : deriv (fun t : ℝ => 3 * t ^ 2 + 1) (x i) = 6 * x i := by
      have : HasDerivAt (fun t : ℝ => 3 * t ^ 2 + 1) (6 * x i) (x i) := by
        have := ((hasDerivAt_pow 2 (x i)).const_mul 3).add_const 1
        convert this using 1
        ring
      exact this.deriv
    rw [this]
  · simp only [hj, ite_false, false_and]
    exact pderiv_const 0 k x

lemma hessGe_quarV (d : ℕ) : HessGe (quarV d) 1 := by
  intro x v
  simp only [pderiv2_quarV, ite_mul, zero_mul]
  have e1 : ∀ i : Fin d, ∑ j, (if j = i then (3 * x i ^ 2 + 1) * v i * v j else 0) =
      (3 * x i ^ 2 + 1) * v i * v i := fun i => by simp
  simp only [e1]
  rw [one_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [mul_nonneg (sq_nonneg (x i)) (sq_nonneg (v i))]

/-- the separable quartic Gibbs data on `ℝ^d` (`Hess V ≥ I`, `ρ = 1 > 0`; `e^{-V}` integrable by `ofConvex`). -/
noncomputable def quarData (d : ℕ) : GibbsRdData d :=
  GibbsRdData.ofConvex (sm_quarV d) (by norm_num : (0 : ℝ) < 1) (hessGe_quarV d)

lemma quarData_V (d : ℕ) : (quarData d).V = quarV d := rfl

lemma abs_cube_add (t : ℝ) : |t ^ 3 + t| = |t| ^ 3 + |t| := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by positivity)]
  · rw [abs_of_nonpos h, abs_of_nonpos (by nlinarith [sq_nonneg t])]
    ring

lemma abs_le_gradL1 (x : Rd d) (i : Fin d) : |x i| ^ 3 + |x i| ≤ gradL1 (quarV d) x := by
  have : |pderiv (quarV d) i x| ≤ gradL1 (quarV d) x :=
    Finset.single_le_sum (f := fun k => |pderiv (quarV d) k x|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  rwa [pderiv_quarV, abs_cube_add] at this

theorem quarData_growHess3 (d : ℕ) : (quarData d).GrowHess3 := by
  refine ⟨⟨3, fun x i j => ?_⟩, ⟨6, fun x i j k => ?_⟩⟩
  · show |pderiv (pderiv (quarV d) i) j x| ≤ 3 * (1 + gradL1 (quarV d) x)
    rw [pderiv2_quarV]
    have h := abs_le_gradL1 x i
    have ha := abs_nonneg (x i)
    have hsq : |x i| ^ 2 ≤ 1 + |x i| ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (|x i| - 1)) (by linarith : 0 ≤ |x i| + 1)]
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      have : x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
      nlinarith
    · simp only [abs_zero]
      nlinarith [gradL1_nonneg (quarV d) x]
  · show |pderiv (pderiv (pderiv (quarV d) i) j) k x| ≤ 6 * (1 + gradL1 (quarV d) x)
    rw [pderiv3_quarV]
    have h := abs_le_gradL1 x i
    have ha := abs_nonneg (x i)
    split_ifs
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      nlinarith [pow_nonneg ha 3]
    · simp only [abs_zero]
      nlinarith [gradL1_nonneg (quarV d) x]

/-- `V''` is unbounded (`d ≥ 1`): the R18 hypothesis `BddHess3` fails. -/
theorem quarData_not_bddHess3 (d : ℕ) : ¬ (quarData (d + 1)).BddHess3 := by
  rintro ⟨⟨C, hC⟩, -⟩
  have := hC (fun _ => |C| + 1) 0 0
  change |pderiv (pderiv (quarV (d + 1)) 0) 0 _| ≤ C at this
  rw [pderiv2_quarV] at this
  simp only [ite_true] at this
  have h1 : (0 : ℝ) ≤ |C| := abs_nonneg C
  have h2 := le_abs_self C
  rw [abs_of_nonneg (by positivity)] at this
  nlinarith [sq_nonneg (|C| + 1)]

/-- **C6**: a `ρ = 1 > 0` witness of the weighted theorem, outside `BddHess3` (`∇V ~ x³`, `∇²V ~ x²`, `∇³V ~ x`). -/
theorem quarData_witness (d : ℕ) :
    (quarData d).GrowHess3 ∧ HessGe (quarData d).V 1 ∧ ¬ (quarData (d + 1)).BddHess3 :=
  ⟨quarData_growHess3 d, hessGe_quarV d, quarData_not_bddHess3 d⟩

theorem quarData_core2 (d : ℕ) : (quarData d).gibbsRdFull_unconditional.Core2 :=
  (quarData d).gibbsRd_core2_w (hessGe_quarV d) (quarData_growHess3 d)

/-- the converse of Prop. 3.3.17 for the quartic potential `Σ xᵢ⁴/4 + xᵢ²/2` (`ρ = 1`). -/
theorem quarData_mem_domain_of_Γ₂ (d : ℕ) {f : Rd d → ℝ}
    (hf : f ∈ (quarData d).gibbsRdFull_unconditional.A) (hf2 : MemLp f 2 (quarData d).toEll.μ)
    (hG : Integrable (FullTriple.G (quarData d).gibbsRdFull_unconditional f f) (quarData d).toEll.μ)
    (hG2 : Integrable ((quarData d).gibbsRdFull_unconditional.toDiffusionTriple.Γ₂ f f)
      (quarData d).toEll.μ) :
    ∃ hF : hf2.toLp f ∈ (quarData d).gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      (((quarData d).gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 (quarData d).toEll.μ) : Rd d → ℝ) =ᵐ[(quarData d).toEll.μ]
        (quarData d).gibbsRdFull_unconditional.L f :=
  (quarData d).gibbsRd_mem_domain_of_Γ₂_w (hessGe_quarV d) (quarData_growHess3 d) hf hf2 hG hG2

/-- the older examples also satisfy the weaker hypothesis (`BddHess3 ⇒ GrowHess3`). -/
theorem gaussData_growHess3 (d : ℕ) : (gaussData d).GrowHess3 := (gaussData_bddHess3 d).growHess3

end MarkovTriple.BGL.Instances.GibbsRd
