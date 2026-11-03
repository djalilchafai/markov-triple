import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Gibbs

/-!
# Bochner identity on `ℝ^d` with a Gibbs weight (BGL (1.16.5)) and the curvature `Hess V ≥ ρ`

For the Gibbs generator `L = Δ − ∇V·∇` on `ℝ^d` and `f` of class `C^∞`, everywhere on `ℝ^d`:
`Γ₂(f) = ½ (L Γ(f) − 2 Γ(f, L f)) = Σᵢⱼ (∂ⱼ∂ᵢ f)² + Σᵢⱼ ∂ⱼ∂ᵢV ∂ᵢf ∂ⱼf = ‖Hess f‖² + Hess V (∇f,∇f)`.
Hence `Hess V ≥ ρ ⇒ ρ Γ(f) ≤ Γ₂(f)`, i.e. `Curv ρ` (`CD(ρ,∞)` of Def. 3.3.14 on `C^∞`).  The commutation
`∂ᵢ∂ᵢ∂ₖ f = ∂ₖ∂ᵢ∂ᵢ f` uses the symmetry of the second derivative (`pderiv_symm`).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

/-- the finite-sum algebra behind the Bochner identity (all indices are coordinates). -/
lemma alg_bochner {n : ℕ} (df dV : Fin n → ℝ) (H HV T : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) :
    (∑ i, (∑ k, ((T k i * df k + H k i * H k i) + (H k i * H k i + df k * T k i)) -
        dV i * ∑ k, (H k i * df k + df k * H k i)) -
      ∑ k, df k * ∑ j, (T k j - (HV j k * df j + dV j * H j k)) -
        ∑ k, df k * ∑ j, (T k j - (HV j k * df j + dV j * H j k))) / 2 =
      ∑ i, ∑ j, H i j ^ 2 + ∑ i, ∑ j, HV i j * df i * df j := by
  have e1 : ∀ i, (∑ k, ((T k i * df k + H k i * H k i) + (H k i * H k i + df k * T k i)) -
        dV i * ∑ k, (H k i * df k + df k * H k i)) =
      ∑ k, (((T k i * df k + H k i * H k i) + (H k i * H k i + df k * T k i)) -
        dV i * (H k i * df k + df k * H k i)) := by
    intro i
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  have e2 : ∑ k, df k * ∑ j, (T k j - (HV j k * df j + dV j * H j k)) =
      ∑ i, ∑ k, df k * (T k i - (HV i k * df i + dV i * H i k)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have e3 : ∑ i, ∑ j, H i j ^ 2 = ∑ i, ∑ k, H k i ^ 2 := Finset.sum_comm
  have e4 : ∑ i, ∑ j, HV i j * df i * df j = ∑ i, ∑ k, df k * (HV i k * df i) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [e1, e2]
  rw [e3, e4]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hH i k]
  ring

section Calc
variable {V f : Rd d → ℝ}

lemma sm_Gr (hf : Sm f) : Sm (Gr f f) :=
  ContDiff.sum fun k _ => (hf.pderiv k).mul (hf.pderiv k)

lemma sm_Lr (hV : Sm V) (hf : Sm f) : Sm (Lr V f) :=
  ContDiff.sum fun i _ => ((hf.pderiv i).pderiv i).sub ((hV.pderiv i).mul (hf.pderiv i))

/-- `∂ᵢ|∇f|² = 2 Σₖ ∂ₖf ∂ᵢ∂ₖf` -/
lemma pderiv_Gr (hf : Sm f) (i : Fin d) (y : Rd d) :
    pderiv (Gr f f) i y = ∑ k, (pderiv (pderiv f k) i y * pderiv f k y +
      pderiv f k y * pderiv (pderiv f k) i y) := by
  unfold Gr
  rw [pderiv_sum _ (fun k => (hf.pderiv k).mul (hf.pderiv k)) i y]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact pderiv_mul' (hf.pderiv k) (hf.pderiv k) i y

/-- the third derivatives commute: `∂ₖ∂ⱼ∂ⱼ f = ∂ⱼ∂ⱼ∂ₖ f`. -/
lemma third_symm (hf : Sm f) (j k : Fin d) (x : Rd d) :
    pderiv (pderiv (pderiv f j) j) k x = pderiv (pderiv (pderiv f k) j) j x := by
  have h1 : pderiv (pderiv (pderiv f j) j) k x = pderiv (pderiv (pderiv f j) k) j x :=
    pderiv_symm (hf.pderiv j) j k x
  rw [h1, pderiv_symm_fun hf j k]

end Calc

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- `∂ₖ(L f)` for the Gibbs generator. -/
lemma pderiv_Lr {f : Rd d → ℝ} (hf : Sm f) (k : Fin d) (x : Rd d) :
    pderiv (Lr G.V f) k x = ∑ j, (pderiv (pderiv (pderiv f j) j) k x -
      (pderiv (pderiv G.V j) k x * pderiv f j x + pderiv G.V j x * pderiv (pderiv f j) k x)) := by
  unfold Lr
  rw [pderiv_sum _ (fun j => ((hf.pderiv j).pderiv j).sub ((G.smooth.pderiv j).mul (hf.pderiv j))) k x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_sub' ((hf.pderiv j).pderiv j) ((G.smooth.pderiv j).mul (hf.pderiv j)) k x,
    pderiv_mul' (G.smooth.pderiv j) (hf.pderiv j) k x]

/-- **Bochner identity on `ℝ^d`** (BGL (1.16.5)): `Γ₂(f) = ‖Hess f‖² + Hess V(∇f,∇f)` for `C^∞` `f`. -/
theorem gibbsRd_Γ₂_eq {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) :
    G.gibbsRdDiff.Γ₂ f f x = ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 +
      ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x := by
  set E := G.toEll with hE
  have hΓ₂ : G.gibbsRdDiff.Γ₂ f f x =
      (E.L (E.Γ f f) x - E.Γ f (E.L f) x - E.Γ (E.L f) f x) / 2 := by
    have := congrFun (E.Γ₂_eq_comb hf) x
    exact this
  have e1 : E.Γ f f = Gr f f := G.toEll_Γ f f
  have e2 : E.L f = Lr G.V f := G.toEll_L hf
  have e3 : E.L (Gr f f) = Lr G.V (Gr f f) := G.toEll_L (sm_Gr hf)
  rw [hΓ₂, e1, e3, e2, G.toEll_Γ f (Lr G.V f), G.toEll_Γ (Lr G.V f) f]
  have hA : ∀ i, pderiv (pderiv (Gr f f) i) i x = ∑ k, ((pderiv (pderiv (pderiv f k) i) i x *
      pderiv f k x + pderiv (pderiv f k) i x * pderiv (pderiv f k) i x) +
      (pderiv (pderiv f k) i x * pderiv (pderiv f k) i x +
        pderiv f k x * pderiv (pderiv (pderiv f k) i) i x)) := by
    intro i
    have hfun : pderiv (Gr f f) i = fun y => ∑ k, (pderiv (pderiv f k) i y * pderiv f k y +
        pderiv f k y * pderiv (pderiv f k) i y) := funext fun y => pderiv_Gr hf i y
    rw [hfun, pderiv_sum _ (fun k => (((hf.pderiv k).pderiv i).mul (hf.pderiv k)).add
      ((hf.pderiv k).mul ((hf.pderiv k).pderiv i))) i x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pderiv_add' (((hf.pderiv k).pderiv i).mul (hf.pderiv k))
      ((hf.pderiv k).mul ((hf.pderiv k).pderiv i)) i x,
      pderiv_mul' ((hf.pderiv k).pderiv i) (hf.pderiv k) i x,
      pderiv_mul' (hf.pderiv k) ((hf.pderiv k).pderiv i) i x]
  have hLΓ : Lr G.V (Gr f f) x = ∑ i, (∑ k, ((pderiv (pderiv (pderiv f k) i) i x *
      pderiv f k x + pderiv (pderiv f k) i x * pderiv (pderiv f k) i x) +
      (pderiv (pderiv f k) i x * pderiv (pderiv f k) i x +
        pderiv f k x * pderiv (pderiv (pderiv f k) i) i x)) -
      pderiv G.V i x * ∑ k, (pderiv (pderiv f k) i x * pderiv f k x +
        pderiv f k x * pderiv (pderiv f k) i x)) := by
    unfold Lr
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA i, pderiv_Gr hf i x]
  have hGL : Gr f (Lr G.V f) x = ∑ k, pderiv f k x * ∑ j, (pderiv (pderiv (pderiv f k) j) j x -
      (pderiv (pderiv G.V j) k x * pderiv f j x + pderiv G.V j x * pderiv (pderiv f j) k x)) := by
    unfold Gr
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [G.pderiv_Lr hf k x]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [third_symm hf j k x]
  have hGL' : Gr (Lr G.V f) f x = Gr f (Lr G.V f) x := by
    unfold Gr
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hGL', hLΓ, hGL]
  exact alg_bochner (fun k => pderiv f k x) (fun i => pderiv G.V i x)
    (fun k i => pderiv (pderiv f k) i x) (fun j k => pderiv (pderiv G.V j) k x)
    (fun k i => pderiv (pderiv (pderiv f k) i) i x) (fun i j => pderiv_symm hf i j x)

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
