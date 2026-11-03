import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Main

/-!
# Weighted Riemannian manifolds in a global chart `ℝ^d`: BGL's coordinate definitions

BGL Sect. 1.11.3 (pp. 46–47) works with the **co-metric** `g = (g^{ij}(x))`, the Riemannian measure with density
`w_g = det(g)^{-1/2}` with respect to Lebesgue measure, the Laplace–Beltrami operator
`Δ_g f = (1/w_g) Σᵢⱼ ∂ᵢ(w_g g^{ij} ∂ⱼ f)` and the weighted Laplacian `L = Δ_g − ∇W·∇` symmetric for
`dμ = e^{-W} dμ_g` ((1.11.10)).  `RiemData d` records exactly this data in the single global chart `ℝ^d`:
a smooth symmetric positive definite co-metric admitting a proper smooth function of `g`-gradient `≤ 1` (the
completeness criterion `g_exh`; round 17: this replaces the earlier hypothesis that `g^{ij}` be bounded above, which implies it) and a smooth weight `W` with
`e^{-W} w_g` integrable.  `toEll` is the weighted elliptic data `a = g^{ij}`, `w = e^{-W} w_g` of
`GibbsRd/Ell*`; hence `riemDiff := toEll.diff` and all of its theory.

Proved here: `riem_L_eq` (the formula (1.11.10) `L = Δ_g − ∇W·∇`), `ell_L_coord` (the coordinate form (1.11.8) with
`∂ᵢ log w`), and the consistency check `ofGibbs`: for `g = δ` the Riemannian operator is the Gibbs one of
`GibbsRd/Gibbs` (`ofGibbs_toEll_L`).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

/-- **Weighted Riemannian data in global coordinates** (BGL Sect. 1.11.3): co-metric `g^{ij}`, potential `W`,
`μ = e^{-W} det(g^{ij})^{-1/2} dx / Z`. -/
structure RiemData (d : ℕ) where
  /-- the co-metric `(g^{ij})` -/
  g : Fin d → Fin d → Rd d → ℝ
  /-- the weight potential `W` -/
  W : Rd d → ℝ
  g_smooth : ∀ i j, Sm (g i j)
  g_symm : ∀ i j x, g i j x = g j i x
  g_posDef : ∀ x, (Matrix.of fun i j => g i j x).PosDef
  /-- **completeness criterion** (round 17: replaces the former bound `g ≤ Λ`, which implies it, `exh_of_bdd`): a smooth
  nonnegative proper function `ψ` (bounded sublevel sets) of `g`-gradient `Σ gᵢⱼ ∂ᵢψ ∂ⱼψ ≤ 1`, i.e. a smoothed
  Riemannian distance; the standard criterion for completeness of the chart -/
  g_exh : ∃ ψ : Rd d → ℝ, Sm ψ ∧ (∀ x, 0 ≤ ψ x) ∧ (∀ c : ℝ, Bornology.IsBounded {x : Rd d | ψ x ≤ c}) ∧
    ∀ x, ∑ i, ∑ j, g i j x * pderiv ψ i x * pderiv ψ j x ≤ 1
  W_smooth : Sm W
  /-- the measure `e^{-W} dμ_g` is finite -/
  integrable : Integrable (fun x => Real.exp (-W x) *
    (Matrix.det (Matrix.of fun i j => g i j x)) ^ (-(1 / 2 : ℝ))) volume

namespace RiemData
variable (R : RiemData d)

/-- the matrix `(g^{ij}(x))` -/
noncomputable def mat (x : Rd d) : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => R.g i j x

/-- `det (g^{ij})` -/
noncomputable def detg (x : Rd d) : ℝ := (R.mat x).det

lemma detg_pos (x : Rd d) : 0 < R.detg x := (R.g_posDef x).det_pos

lemma sm_detg : Sm R.detg := by
  have : R.detg = fun x => ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, R.g (σ i) i x := by
    funext x
    unfold detg mat
    rw [Matrix.det_apply']
    rfl
  rw [this]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => R.g_smooth (σ i) i)

/-- the Riemannian density `w_g = det(g^{ij})^{-1/2}` with respect to Lebesgue measure -/
noncomputable def wg (x : Rd d) : ℝ := R.detg x ^ (-(1 / 2 : ℝ))

lemma wg_pos (x : Rd d) : 0 < R.wg x := Real.rpow_pos_of_pos (R.detg_pos x) _

lemma sm_wg : Sm R.wg := R.sm_detg.rpow_const_of_ne fun x => (R.detg_pos x).ne'

/-- the full density `e^{-W} w_g` -/
noncomputable def wt (x : Rd d) : ℝ := Real.exp (-R.W x) * R.wg x

lemma sm_wt : Sm R.wt := (R.W_smooth.neg.exp).mul R.sm_wg

/-- the quadratic form of the co-metric is positive -/
lemma quad_pos (x v : Rd d) (hv : v ≠ 0) : 0 < ∑ i, ∑ j, R.g i j x * v i * v j := by
  have h := (Matrix.posDef_iff_dotProduct_mulVec.1 (R.g_posDef x)).2 hv
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial] at h
  refine h.trans_le (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The weighted elliptic data of `R`**: `a = g^{ij}`, `w = e^{-W} det(g^{ij})^{-1/2}`. -/
noncomputable def toEll : EllData d where
  a := R.g
  w := R.wt
  a_smooth := R.g_smooth
  a_symm := R.g_symm
  a_pos := R.quad_pos
  a_exh := R.g_exh
  w_smooth := R.sm_wt
  w_pos := fun x => mul_pos (Real.exp_pos _) (R.wg_pos x)
  integrable := R.integrable

/-- the Riemannian carré du champ `Γ(f,g) = Σ g^{ij} ∂ᵢf ∂ⱼg` -/
noncomputable abbrev Γ (f h : Rd d → ℝ) : Rd d → ℝ := R.toEll.Γ f h

/-- the Laplace–Beltrami operator `Δ_g f = (1/w_g) Σᵢ ∂ᵢ(w_g Σⱼ g^{ij} ∂ⱼ f)` (BGL Sect. 1.11.3) -/
noncomputable def Δg (f : Rd d → ℝ) : Rd d → ℝ :=
  fun x => (R.wg x)⁻¹ * ∑ i, pderiv (fun y => R.wg y * ∑ j, R.g i j y * pderiv f j y) i x

/-- **The Riemannian `DiffusionTriple`** (D1–D8) of `R`: `Γ(f,g) = Σ g^{ij}∂ᵢf ∂ⱼg`, `L = Δ_g − ∇W·∇` (`riem_L_eq`),
`μ = e^{-W} dμ_g / Z`, `𝒜₀ = C_c^∞(ℝ^d)`. -/
noncomputable def riemDiff : DiffusionTriple (Rd d) := R.toEll.diff

/-- completeness (BGL Def. 3.3.9) of the weighted Riemannian chart -/
theorem riemDiff_isComplete : R.riemDiff.IsComplete := R.toEll.diff_isComplete

lemma pderiv_exp_neg (i : Fin d) (x : Rd d) :
    pderiv (fun y => Real.exp (-R.W y)) i x = Real.exp (-R.W x) * (-pderiv R.W i x) := by
  have h : HasFDerivAt (fun y => Real.exp (-R.W y)) (Real.exp (-R.W x) • (-(fderiv ℝ R.W x))) x :=
    (R.W_smooth.hasFDerivAt' x).neg.exp
  unfold pderiv
  rw [h.fderiv]
  simp

/-- **(1.11.10)**: `L f = Δ_g f − Σᵢⱼ g^{ij} ∂ᵢW ∂ⱼ f = Δ_g f − ∇W·∇f`, for `C^∞` `f`. -/
theorem riem_L_eq {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) :
    R.toEll.L f x = R.Δg f x - ∑ i, ∑ j, R.g i j x * pderiv R.W i x * pderiv f j x := by
  have hQ : ∀ i, Sm (fun y => R.wg y * ∑ j, R.g i j y * pderiv f j y) := fun i =>
    R.sm_wg.mul (ContDiff.sum fun j _ => (R.g_smooth i j).mul (hf.pderiv j))
  have hP : ∀ i, R.toEll.P f i = fun y => Real.exp (-R.W y) *
      (R.wg y * ∑ j, R.g i j y * pderiv f j y) := by
    intro i; funext y
    simp only [EllData.P, toEll, wt]; ring
  have hD : ∀ i, pderiv (R.toEll.P f i) i x = Real.exp (-R.W x) * (-pderiv R.W i x) *
      (R.wg x * ∑ j, R.g i j x * pderiv f j x) +
      Real.exp (-R.W x) * pderiv (fun y => R.wg y * ∑ j, R.g i j y * pderiv f j y) i x := by
    intro i
    rw [hP i, pderiv_mul' (f := fun y => Real.exp (-R.W y)) R.W_smooth.neg.exp (hQ i) i x,
      R.pderiv_exp_neg]
  have hwt : R.toEll.w x = Real.exp (-R.W x) * R.wg x := rfl
  have hne : Real.exp (-R.W x) ≠ 0 := (Real.exp_pos _).ne'
  have hwg : R.wg x ≠ 0 := (R.wg_pos x).ne'
  rw [EllData.L_eq]
  simp only [hD, hwt]
  unfold Δg
  rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have e1 : ∑ i, (Real.exp (-R.W x) * R.wg x)⁻¹ * (Real.exp (-R.W x) * pderiv (fun y => R.wg y *
      ∑ j, R.g i j y * pderiv f j y) i x) = ∑ i, (R.wg x)⁻¹ * pderiv (fun y => R.wg y *
      ∑ j, R.g i j y * pderiv f j y) i x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have e2 : ∑ i, (Real.exp (-R.W x) * R.wg x)⁻¹ * (Real.exp (-R.W x) * (-pderiv R.W i x) *
      (R.wg x * ∑ j, R.g i j x * pderiv f j x)) =
      -∑ i, ∑ j, R.g i j x * pderiv R.W i x * pderiv f j x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (Real.exp (-R.W x) * R.wg x)⁻¹ * (Real.exp (-R.W x) * (-pderiv R.W i x) *
        (R.wg x * ∑ j, R.g i j x * pderiv f j x)) =
        -(pderiv R.W i x * ∑ j, R.g i j x * pderiv f j x) := by
      field_simp
    rw [this, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  ring

end RiemData

/-! ### Coordinate form (1.11.8) for any weighted elliptic operator -/

section ell
variable {E : EllData d}

lemma ell_pderiv_log_w (i : Fin d) (x : Rd d) :
    pderiv (fun y => Real.log (E.w y)) i x = pderiv E.w i x / E.w x := by
  have h := (E.w_smooth.hasFDerivAt' x).log (E.w_pos x).ne'
  unfold pderiv
  rw [h.fderiv]
  simp [div_eq_inv_mul]

/-- **BGL (1.11.8)**: `L f = Σᵢⱼ g^{ij} ∂ᵢ∂ⱼ f + Σⱼ (Σᵢ ∂ᵢ g^{ij} + Σᵢ g^{ij} ∂ᵢ log w) ∂ⱼ f`. -/
theorem ell_L_coord {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) :
    E.L f x = ∑ i, ∑ j, E.a i j x * pderiv (pderiv f j) i x +
      ∑ j, (∑ i, pderiv (E.a i j) i x +
        ∑ i, E.a i j x * pderiv (fun y => Real.log (E.w y)) i x) * pderiv f j x := by
  have hS : ∀ i, Sm (fun y => ∑ j, E.a i j y * pderiv f j y) := fun i =>
    ContDiff.sum fun j _ => (E.a_smooth i j).mul (hf.pderiv j)
  have hD : ∀ i, pderiv (E.P f i) i x = pderiv E.w i x * ∑ j, E.a i j x * pderiv f j x +
      E.w x * ∑ j, (pderiv (E.a i j) i x * pderiv f j x + E.a i j x * pderiv (pderiv f j) i x) := by
    intro i
    have : E.P f i = fun y => E.w y * ∑ j, E.a i j y * pderiv f j y := rfl
    rw [this, pderiv_mul' E.w_smooth (hS i) i x,
      pderiv_sum _ (fun j => (E.a_smooth i j).mul (hf.pderiv j)) i x]
    congr 2
    exact Finset.sum_congr rfl fun j _ => pderiv_mul' (E.a_smooth i j) (hf.pderiv j) i x
  have hw : E.w x ≠ 0 := (E.w_pos x).ne'
  rw [E.L_eq]
  simp only [hD, ell_pderiv_log_w]
  rw [Finset.sum_add_distrib, mul_add]
  have e1 : (E.w x)⁻¹ * ∑ i, E.w x * ∑ j, (pderiv (E.a i j) i x * pderiv f j x +
      E.a i j x * pderiv (pderiv f j) i x) =
      ∑ i, ∑ j, (pderiv (E.a i j) i x * pderiv f j x + E.a i j x * pderiv (pderiv f j) i x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have e2 : (E.w x)⁻¹ * ∑ i, pderiv E.w i x * ∑ j, E.a i j x * pderiv f j x =
      ∑ i, ∑ j, E.a i j x * (pderiv E.w i x / E.w x) * pderiv f j x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [e1, e2]
  have e3 : ∑ i, ∑ j, (pderiv (E.a i j) i x * pderiv f j x + E.a i j x * pderiv (pderiv f j) i x) =
      ∑ i, ∑ j, pderiv (E.a i j) i x * pderiv f j x +
        ∑ i, ∑ j, E.a i j x * pderiv (pderiv f j) i x := by
    simp only [Finset.sum_add_distrib]
  rw [e3]
  have e4 : ∑ j, (∑ i, pderiv (E.a i j) i x +
        ∑ i, E.a i j x * (pderiv E.w i x / E.w x)) * pderiv f j x =
      ∑ i, ∑ j, pderiv (E.a i j) i x * pderiv f j x +
        ∑ i, ∑ j, E.a i j x * (pderiv E.w i x / E.w x) * pderiv f j x := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    rw [Finset.sum_comm]
  rw [e4]
  ring

end ell

/-- the identity matrix as a Kronecker array -/
lemma matrix_of_delta : (Matrix.of fun i j : Fin d => (if i = j then (1 : ℝ) else 0)) = 1 := by
  ext i j; simp [Matrix.one_apply]

namespace RiemData

/-- **Flat consistency check**: a Gibbs datum `e^{-V}` on `ℝ^d` is the Riemannian datum with co-metric `δ`
(`w_g = det(δ)^{-1/2} = 1`). -/
noncomputable def ofGibbs (G : GibbsRdData d) : RiemData d where
  g := fun i j _ => if i = j then 1 else 0
  W := G.V
  g_smooth := fun i j => contDiff_const
  g_symm := fun i j x => by simp [eq_comm]
  g_posDef := fun x => by
    rw [matrix_of_delta]; exact Matrix.PosDef.one
  g_exh := G.toEll.a_exh
  W_smooth := G.smooth
  integrable := by
    simpa [matrix_of_delta] using G.integrable

lemma ofGibbs_toEll_a (G : GibbsRdData d) : (ofGibbs G).toEll.a = G.toEll.a := rfl

lemma ofGibbs_toEll_w (G : GibbsRdData d) : (ofGibbs G).toEll.w = G.toEll.w := by
  funext x
  simp [toEll, wt, wg, detg, mat, ofGibbs, GibbsRdData.toEll, matrix_of_delta]

/-- for `g = δ` the Riemannian generator is the Gibbs generator `Δ − ∇V·∇` (all `f`). -/
theorem ofGibbs_toEll_L (G : GibbsRdData d) (f : Rd d → ℝ) : (ofGibbs G).toEll.L f = G.toEll.L f := by
  funext x
  unfold EllData.L
  rw [ofGibbs_toEll_a, ofGibbs_toEll_w]

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
