import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdDefs
import MarkovTriple.BGL.Instances.GibbsRd.Main

/-!
# Non-vacuity of `BddHess3` with `ρ > 0` (R18, Stream A3, target B6)

(a) the standard Gaussian `V = |x|²/2` (`Hess V = I`, `∇³V = 0`, `∇V` unbounded);
(b) the non-Gaussian `V(x) = |x|²/2 + cos(x₀)/2` on `ℝ^{d+1}`: `Hess V ≥ 1/2`, `|∂ᵢ∂ⱼV| ≤ 2`, `|∂ᵢ∂ⱼ∂ₖV| ≤ 1`.
In both, `Hess V ≥ ρ > 0`, hence `|∇V(x)| → ∞` (`V' ` unbounded): the hypothesis `BddHess3` does not contradict `ρ > 0`
(unlike the 1-D hypothesis `BddJet` of R17, ERRATA R17-M1).
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- `∂ⱼ (g ∘ eval₀) = δ_{j0} g'(x₀)`. -/
lemma pderiv_fun_coord0 (g : ℝ → ℝ) (hg : Differentiable ℝ g) (j : Fin (d + 1)) (x : Rd (d + 1)) :
    pderiv (fun y : Rd (d + 1) => g (y 0)) j x = if j = 0 then deriv g (x 0) else 0 := by
  have h1 : HasFDerivAt (fun y : Rd (d + 1) => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) 0) x := hasFDerivAt_apply 0 x
  have h2 := (hg (x 0)).hasDerivAt.comp_hasFDerivAt x h1
  unfold pderiv
  rw [show (fun y : Rd (d + 1) => g (y 0)) = g ∘ fun y : Rd (d + 1) => y 0 from rfl, h2.fderiv]
  by_cases hj : j = 0 <;> simp [hj]

lemma sm_fun_coord0 (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Sm (fun y : Rd (d + 1) => g (y 0)) :=
  hg.comp (contDiff_apply ℝ ℝ (0 : Fin (d + 1)))

/-! ### (a) the Gaussian -/

lemma pderiv_gauss_fun (i : Fin d) : pderiv (fun y : Rd d => qd y / 2) i = fun y => y i := by
  funext y
  have := pderiv_qd i y
  unfold pderiv at this ⊢
  have hd : HasFDerivAt (qd : Rd d → ℝ) (fderiv ℝ qd y) y := (sm_qd.differentiableAt y).hasFDerivAt
  rw [show (fun y : Rd d => qd y / 2) = fun y => (2 : ℝ)⁻¹ * qd y from by
    funext z; simp [div_eq_inv_mul], (hd.const_mul (2 : ℝ)⁻¹).fderiv]
  simp [this]

lemma gaussData_bddHess3 (d : ℕ) : (gaussData d).BddHess3 := by
  refine ⟨⟨1, fun x i j => ?_⟩, ⟨0, fun x i j k => ?_⟩⟩
  · show |pderiv (pderiv (fun y : Rd d => qd y / 2) i) j x| ≤ 1
    rw [hess_gauss]; split_ifs <;> simp
  · show |pderiv (pderiv (pderiv (fun y : Rd d => qd y / 2) i) j) k x| ≤ 0
    rw [pderiv_gauss_fun i]
    have : pderiv (fun y : Rd d => y i) j = fun _ => if j = i then (1 : ℝ) else 0 :=
      funext fun y => pderiv_coord i j y
    rw [this, pderiv_const]; simp

/-- `Hess V = I ≥ 1 > 0`, `∇V(x) = x` unbounded. -/
theorem gaussData_witness (d : ℕ) :
    (gaussData d).BddHess3 ∧ HessGe (gaussData d).V 1 ∧ ¬ ∃ C : ℝ, ∀ (x : Rd (d + 1)) (i : Fin (d + 1)),
      |pderiv (fun y : Rd (d + 1) => qd y / 2) i x| ≤ C := by
  refine ⟨gaussData_bddHess3 d, hessGe_gauss, ?_⟩
  rintro ⟨C, hC⟩
  have := hC (fun _ => |C| + 1) 0
  rw [pderiv_gauss_fun] at this
  have h := abs_nonneg C
  rw [abs_of_pos (by linarith)] at this
  linarith [le_abs_self C]

/-! ### (b) a non-Gaussian example -/

/-- `V(x) = |x|²/2 + cos(x₀)/2` on `ℝ^{d+1}`. -/
noncomputable def cosV (d : ℕ) : Rd (d + 1) → ℝ := fun x => qd x / 2 + Real.cos (x 0) / 2

lemma sm_cosV (d : ℕ) : Sm (cosV d) :=
  (sm_qd.div_const 2).add (sm_fun_coord0 (fun t => Real.cos t / 2) (Real.contDiff_cos.div_const 2))

lemma pderiv_cosV_fun (d : ℕ) (i : Fin (d + 1)) :
    pderiv (cosV d) i = fun y => y i + (if i = 0 then -Real.sin (y 0) / 2 else 0) := by
  funext y
  unfold cosV
  rw [pderiv_add' (sm_qd.div_const 2) (sm_fun_coord0 (fun t => Real.cos t / 2) (Real.contDiff_cos.div_const 2)),
    pderiv_fun_coord0 (fun t => Real.cos t / 2) ((Real.differentiable_cos).div_const 2), pderiv_gauss_fun]
  simp [Real.deriv_cos]

lemma pderiv2_cosV_fun (d : ℕ) (i j : Fin (d + 1)) (x : Rd (d + 1)) :
    pderiv (pderiv (cosV d) i) j x = (if j = i then 1 else 0) + (if i = 0 ∧ j = 0 then -Real.cos (x 0) / 2 else 0) := by
  rw [pderiv_cosV_fun]
  by_cases hi : i = 0
  · subst hi
    simp only [ite_true]
    rw [pderiv_add' (contDiff_apply ℝ ℝ (0 : Fin (d + 1)))
      (sm_fun_coord0 (fun t => -Real.sin t / 2) ((Real.contDiff_sin.neg).div_const 2)), pderiv_coord,
      pderiv_fun_coord0 (fun t => -Real.sin t / 2) (((Real.differentiable_sin).neg).div_const 2)]
    by_cases hj : j = 0 <;> simp [hj, Real.deriv_sin]
  · simp only [hi, ite_false, add_zero, false_and]
    rw [pderiv_coord]

lemma pderiv3_cosV_fun (d : ℕ) (i j k : Fin (d + 1)) (x : Rd (d + 1)) :
    pderiv (pderiv (pderiv (cosV d) i) j) k x = if i = 0 ∧ j = 0 ∧ k = 0 then Real.sin (x 0) / 2 else 0 := by
  have : pderiv (pderiv (cosV d) i) j = fun y => (if j = i then (1 : ℝ) else 0) +
      (if i = 0 ∧ j = 0 then -Real.cos (y 0) / 2 else 0) := funext fun y => pderiv2_cosV_fun d i j y
  rw [this]
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [ite_true, and_self]
    rw [pderiv_add' contDiff_const (sm_fun_coord0 (fun t => -Real.cos t / 2) ((Real.contDiff_cos.neg).div_const 2)),
      pderiv_const, pderiv_fun_coord0 (fun t => -Real.cos t / 2) (((Real.differentiable_cos).neg).div_const 2)]
    by_cases hk : k = 0 <;> simp [hk, Real.deriv_cos]
  · simp only [h, ite_false, add_zero]
    rw [pderiv_const]
    have : ¬(i = 0 ∧ j = 0 ∧ k = 0) := fun ⟨a, b, _⟩ => h ⟨a, b⟩
    simp [this]

lemma hessGe_cosV (d : ℕ) : HessGe (cosV d) (1 / 2) := by
  intro x v
  simp only [pderiv2_cosV_fun, add_mul, Finset.sum_add_distrib]
  have e1 : ∑ i, ∑ j, (if j = i then (1 : ℝ) else 0) * v i * v j = ∑ i, v i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq]
  have e2 : ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      (if i = 0 ∧ j = 0 then -Real.cos (x 0) / 2 else 0) * v i * v j = -Real.cos (x 0) / 2 * v 0 ^ 2 := by
    rw [Finset.sum_eq_single (0 : Fin (d + 1))]
    · rw [Finset.sum_eq_single (0 : Fin (d + 1))]
      · simp [sq]; ring
      · intro j _ hj; simp [hj]
      · simp
    · intro i _ hi; simp [hi]
    · simp
  rw [e1, e2]
  have h0 : v 0 ^ 2 ≤ ∑ i, v i ^ 2 :=
    Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ 0)
  have hc := Real.neg_one_le_cos (x 0)
  nlinarith [sq_nonneg (v 0), mul_nonneg (sq_nonneg (v 0)) (by linarith [Real.cos_le_one (x 0)] : 0 ≤ 1 - Real.cos (x 0))]

/-- the non-Gaussian Gibbs data `V = |x|²/2 + cos(x₀)/2` on `ℝ^{d+1}`. -/
noncomputable def cosData (d : ℕ) : GibbsRdData (d + 1) :=
  GibbsRdData.ofConvex (sm_cosV d) (by norm_num : (0 : ℝ) < 1 / 2) (hessGe_cosV d)

lemma cosData_bddHess3 (d : ℕ) : (cosData d).BddHess3 := by
  refine ⟨⟨2, fun x i j => ?_⟩, ⟨1, fun x i j k => ?_⟩⟩
  · show |pderiv (pderiv (cosV d) i) j x| ≤ 2
    rw [pderiv2_cosV_fun]
    have h1 := Real.neg_one_le_cos (x 0)
    have h2 := Real.cos_le_one (x 0)
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · show |pderiv (pderiv (pderiv (cosV d) i) j) k x| ≤ 1
    rw [pderiv3_cosV_fun]
    have h1 := Real.sin_le_one (x 0)
    have h2 := Real.neg_one_le_sin (x 0)
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- **B6 (non-vacuity, non-Gaussian)**: `cosData d` is a `GibbsRdData` with `BddHess3` and `Hess V ≥ 1/2 > 0`
(so `∇V` is unbounded, `V` is not a quadratic). -/
theorem cosData_witness (d : ℕ) :
    (cosData d).BddHess3 ∧ HessGe (cosData d).V (1 / 2) :=
  ⟨cosData_bddHess3 d, hessGe_cosV d⟩

end MarkovTriple.BGL.Instances.GibbsRd
