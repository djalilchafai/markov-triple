import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllPI

/-!
# Gibbs measures `e^{-V} dx` on `ℝ^d` with the trivial metric: `L = Δ − ∇V·∇`

BGL Sect. 1.11.3 (1.11.10) with `g = δ`, and the book's weighted `ℝ^n` example (Sect. 1.16, (1.16.5)).
`GibbsRdData d` (smooth `V` with integrable `e^{-V}`) gives the `EllData` `toEll` with `a = δ`, `w = e^{-V}`; the
generic theory of `EllPI.lean` then provides `gibbsRdDiff : DiffusionTriple (Rd d)`, completeness, ESA/ergodicity
under `WeakHypo`, etc.  Here:

* `toEll_Γ`: `Γ(f,g) = Σᵢ ∂ᵢf ∂ᵢg` (all `f,g`), `toEll_L`: `L f = Σᵢ (∂ᵢ∂ᵢ f − ∂ᵢV ∂ᵢ f) = Δ f − ∇V·∇ f` (`C^∞` `f`);
* `gibbsRd_Γ₂_eq` (BGL (1.16.5)): `Γ₂(f) = ‖Hess f‖² + Hess V(∇f,∇f)` for `C^∞` `f`, everywhere;
* `gibbsRd_curv`: `Hess V ≥ ρ ⇒ Curv ρ` (pointwise `Γ₂ ≥ ρ Γ`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

/-- Data of a Gibbs measure `Z⁻¹ e^{-V} dx` on `ℝ^d`: smooth potential with integrable `e^{-V}`. -/
structure GibbsRdData (d : ℕ) where
  /-- the potential -/
  V : Rd d → ℝ
  /-- smooth -/
  smooth : Sm V
  /-- `e^{-V}` is integrable -/
  integrable : Integrable (fun x => Real.exp (-V x)) volume

/-- the book's Gibbs generator `L f = Σᵢ (∂ᵢ∂ᵢ f − ∂ᵢV ∂ᵢ f) = Δ f − ∇V·∇ f` -/
noncomputable def Lr (V : Rd d → ℝ) (f : Rd d → ℝ) : Rd d → ℝ :=
  fun x => ∑ i, (pderiv (pderiv f i) i x - pderiv V i x * pderiv f i x)

/-- the carré du champ `Γ(f,g) = ∇f·∇g` -/
noncomputable def Gr (f g : Rd d → ℝ) : Rd d → ℝ := fun x => ∑ i, pderiv f i x * pderiv g i x

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- the Euclidean `EllData`: `a = δ`, `w = e^{-V}`. -/
noncomputable def toEll : EllData d where
  a := fun i j _ => if i = j then 1 else 0
  w := fun x => Real.exp (-G.V x)
  a_smooth := fun i j => contDiff_const
  a_symm := fun i j x => by simp [eq_comm]
  a_pos := fun x v hv => by
    have : ∑ i, ∑ j, (if i = j then (1 : ℝ) else 0) * v i * v j = ∑ i, v i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [sq]
    rw [this]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h; push Not at h; exact hv (funext h)
    exact lt_of_lt_of_le (by positivity : 0 < v i ^ 2) (Finset.single_le_sum
      (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  a_exh := exh_of_bdd _ ⟨1, fun x v => by
    have : ∑ i, ∑ j, (if i = j then (1 : ℝ) else 0) * v i * v j = ∑ i, v i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [sq]
    rw [this]; simp⟩
  w_smooth := G.smooth.neg.exp
  w_pos := fun x => Real.exp_pos _
  integrable := G.integrable

lemma pderiv_expneg (i : Fin d) (x : Rd d) :
    pderiv (fun y => Real.exp (-G.V y)) i x = Real.exp (-G.V x) * (-pderiv G.V i x) := by
  have h : HasFDerivAt (fun y => Real.exp (-G.V y)) (Real.exp (-G.V x) • (-(fderiv ℝ G.V x))) x :=
    (G.smooth.hasFDerivAt' x).neg.exp
  unfold pderiv
  rw [h.fderiv]
  simp

/-- `Γ(f,g) = Σᵢ ∂ᵢf ∂ᵢg` for the trivial metric (all `f, g`). -/
theorem toEll_Γ (f g : Rd d → ℝ) : G.toEll.Γ f g = Gr f g := by
  funext x
  unfold EllData.Γ Gr
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [toEll]

/-- `L f = Σᵢ (∂ᵢ∂ᵢ f − ∂ᵢV ∂ᵢ f)` for `C^∞` `f`: the book's `Δ − ∇V·∇` (1.11.10). -/
theorem toEll_L {f : Rd d → ℝ} (hf : Sm f) : G.toEll.L f = Lr G.V f := by
  funext x
  unfold EllData.L Lr
  have hP : ∀ i, (fun y => G.toEll.w y * ∑ j, G.toEll.a i j y * pderiv f j y) =
      fun y => Real.exp (-G.V y) * pderiv f i y := by
    intro i; funext y
    simp [toEll]
  simp only [hP]
  have hm : ∀ i, pderiv (fun y => Real.exp (-G.V y) * pderiv f i y) i x =
      Real.exp (-G.V x) * (-pderiv G.V i x) * pderiv f i x +
        Real.exp (-G.V x) * pderiv (pderiv f i) i x := fun i => by
    rw [pderiv_mul' (f := fun y => Real.exp (-G.V y)) (g := pderiv f i) G.smooth.neg.exp (hf.pderiv i) i x,
      G.pderiv_expneg]
  simp only [hm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Real.exp (-G.V x) ≠ 0 := (Real.exp_pos _).ne'
  show (Real.exp (-G.V x))⁻¹ * _ = _
  field_simp
  ring

/-- **The Gibbs `DiffusionTriple` on `ℝ^d`** (BGL D1–D8): `μ = Z⁻¹ e^{-V} dx`, `𝒜₀ = C_c^∞`,
`L = Δ − ∇V·∇`, `Γ = ∇f·∇g` (see `toEll_L`, `toEll_Γ`). -/
noncomputable def gibbsRdDiff : DiffusionTriple (Rd d) := G.toEll.diff

/-- completeness (BGL Def. 3.3.9) -/
theorem gibbsRdDiff_isComplete : G.gibbsRdDiff.IsComplete := G.toEll.diff_isComplete

theorem gibbsRdDiff_Γ (f g : Rd d → ℝ) : G.gibbsRdDiff.Γ f g = Gr f g := G.toEll_Γ f g

theorem gibbsRdDiff_L {f : Rd d → ℝ} (hf : Sm f) : G.gibbsRdDiff.L f = Lr G.V f := G.toEll_L hf

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
