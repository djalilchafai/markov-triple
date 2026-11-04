import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.DirectRiemHess

/-!
# Direct converse of BGL Prop. 3.3.17: every `EllData d` is a weighted Riemannian chart (R20, Stream D2)

Statements: `STATEMENTS_R20_DirectEll.md` (D4).

## DIFFERENCE FROM BGL

BGL's converse (Prop. 3.3.17, p. 162) goes through `Core2` (ERRATA R15-1); R19 proved `Core2` for `EllData` under the extra
hypothesis `CoreCut`.  The direct route of Stream D2 (cut-off identity for `Γ₂`, `GibbsRd/DirectEllCore.lean`) needs the Hessian
Cauchy–Schwarz `HessCS ρ`, which is proved in a Riemannian chart (`riem_hessCS`).  A general weighted elliptic operator
`L = w⁻¹ div(w a ∇ ·)` with `a` smooth symmetric positive definite and `w > 0` smooth integrable is the weighted Laplacian of the
metric `a⁻¹` with potential `W = log(det(a)^{-1/2}/w)` (BGL Sect. 1.11.3 read backwards), so `EllData d = RiemData d` up to this
bijection (`toRiem_toEll : E.toRiem.toEll = E`).  Hence `HessCS ρ` holds for EVERY `E : EllData d` with `Curv ρ`
(`hessCS_of_curv`), with no hypothesis other than `Curv ρ`; completeness `a_exh` is carried over to `g_exh` unchanged.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL.Instances.Riemannian
open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- two `EllData` with the same `a` and `w` are equal -/
lemma EllData.ext' {E₁ E₂ : EllData d} (ha : E₁.a = E₂.a) (hw : E₁.w = E₂.w) : E₁ = E₂ := by
  cases E₁
  cases E₂
  simp only at ha hw
  subst ha
  subst hw
  rfl

namespace EllData
variable (E : EllData d)

/-- `det (a(x))` -/
noncomputable def detA (x : Rd d) : ℝ := Matrix.det (Matrix.of fun i j => E.a i j x)

lemma posDef_a (x : Rd d) : (Matrix.of fun i j => E.a i j x).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, E.a_symm j i x]
  · have h := E.a_pos x v hv
    refine lt_of_lt_of_le h (le_of_eq ?_)
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

lemma detA_pos (x : Rd d) : 0 < E.detA x := (E.posDef_a x).det_pos

lemma sm_detA : Sm E.detA := by
  have : E.detA = fun x => ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, E.a (σ i) i x := by
    funext x
    unfold detA
    rw [Matrix.det_apply']
    rfl
  rw [this]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => E.a_smooth (σ i) i)

/-- the Riemannian density `det(a)^{-1/2}` -/
noncomputable def wgE (x : Rd d) : ℝ := E.detA x ^ (-(1 / 2 : ℝ))

lemma wgE_pos (x : Rd d) : 0 < E.wgE x := Real.rpow_pos_of_pos (E.detA_pos x) _

lemma sm_wgE : Sm E.wgE := E.sm_detA.rpow_const_of_ne fun x => (E.detA_pos x).ne'

/-- the weight potential `W = log(det(a)^{-1/2} / w)`, so that `e^{-W} det(a)^{-1/2} = w` -/
noncomputable def Wr (x : Rd d) : ℝ := Real.log (E.wgE x / E.w x)

lemma sm_Wr : Sm E.Wr :=
  (E.sm_wgE.div E.w_smooth fun x => (E.w_pos x).ne').log fun x =>
    (div_pos (E.wgE_pos x) (E.w_pos x)).ne'

lemma exp_neg_Wr_mul (x : Rd d) : Real.exp (-E.Wr x) * E.wgE x = E.w x := by
  unfold Wr
  rw [Real.exp_neg, Real.exp_log (div_pos (E.wgE_pos x) (E.w_pos x))]
  have := (E.wgE_pos x).ne'
  field_simp

/-- **D4**: every weighted elliptic datum is a weighted Riemannian chart (`g = a`, `W = log(det(a)^{-1/2}/w)`). -/
noncomputable def toRiem : RiemData d where
  g := E.a
  W := E.Wr
  g_smooth := E.a_smooth
  g_symm := E.a_symm
  g_posDef := E.posDef_a
  g_exh := E.a_exh
  W_smooth := E.sm_Wr
  integrable := by
    have h : (fun x => Real.exp (-E.Wr x) *
        (Matrix.det (Matrix.of fun i j => E.a i j x)) ^ (-(1 / 2 : ℝ))) = E.w :=
      funext fun x => E.exp_neg_Wr_mul x
    rw [h]
    exact E.integrable

theorem toRiem_toEll : E.toRiem.toEll = E :=
  EllData.ext' rfl (funext fun x => E.exp_neg_Wr_mul x)

/-- **D4**: the Hessian Cauchy–Schwarz holds for every `E : EllData d` with `Curv ρ`. -/
theorem hessCS_of_curv {ρ : ℝ} (hρ : E.Curv ρ) : E.HessCS ρ := by
  have hR : E.toRiem.Curv ρ := by
    show E.toRiem.toEll.Curv ρ
    rw [E.toRiem_toEll]
    exact hρ
  have := E.toRiem.riem_hessCS hR
  rwa [E.toRiem_toEll] at this

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
