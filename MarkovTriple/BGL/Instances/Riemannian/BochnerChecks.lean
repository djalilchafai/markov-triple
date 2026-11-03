import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.BochnerCrit

/-!
# Hand checks of the Bochner formula: dimension one, the flat case, and agreement with (1.16.5)

* `riem_self`: `R_{ii}{}^k{}_l = 0` (antisymmetry in the first pair, immediate from the definition); `ricci_fin_one`:
  in dimension `d = 1` every `RiemData` has `Ric = 0` (BGL App. C.3: "in dimension one there is only one metric after a
  change of variables, the usual flat one");
* `ofGibbs`: for the flat co-metric `δ` the Christoffel symbols and the curvature vanish (`ofGibbs_chr`, `ofGibbs_riem`,
  `ofGibbs_ricci`), `hess` is the plain Hessian, and `riem_bochner` reduces to `gibbsRd_Γ₂_eq`'s right-hand side, i.e. the
  Euclidean Bochner formula (1.16.5): `ofGibbs_bochner`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

lemma riem_self (i k l : Fin d) (x : Rd d) : R.riem i i k l x = 0 := by
  unfold riem
  simp

lemma ricci_eq_zero_of_subsingleton [Subsingleton (Fin d)] (i j : Fin d) (x : Rd d) : R.ricci i j x = 0 := by
  unfold ricci
  refine Finset.sum_eq_zero fun k _ => ?_
  have : k = i := Subsingleton.elim _ _
  subst this
  exact R.riem_self _ _ _ x

end RiemData

/-- **Dimension one**: `Ric = 0` for every co-metric `g^{11}(x)` on `ℝ` -/
lemma ricci_fin_one (R : RiemData 1) (i j : Fin 1) (x : Rd 1) : R.ricci i j x = 0 :=
  R.ricci_eq_zero_of_subsingleton i j x

namespace RiemData

/-! ### The flat case -/

section flat
variable (G : GibbsRdData d)

lemma ofGibbs_gl (i j : Fin d) (x : Rd d) : (ofGibbs G).gl i j x = if i = j then 1 else 0 := by
  unfold gl
  have : (ofGibbs G).mat x = 1 := by
    unfold mat
    exact matrix_of_delta
  rw [this, inv_one]
  simp [Matrix.one_apply]

lemma ofGibbs_gl_fun (i j : Fin d) : (ofGibbs G).gl i j = fun _ => if i = j then 1 else 0 :=
  funext fun x => ofGibbs_gl G i j x

lemma ofGibbs_chr1 (q i j : Fin d) (x : Rd d) : (ofGibbs G).chr1 q i j x = 0 := by
  unfold chr1
  simp [ofGibbs_gl_fun, pderiv_const]

lemma ofGibbs_chr (k i j : Fin d) (x : Rd d) : (ofGibbs G).chr k i j x = 0 := by
  unfold chr
  simp [ofGibbs_chr1]

lemma ofGibbs_chr_fun (k i j : Fin d) : (ofGibbs G).chr k i j = fun _ => 0 :=
  funext fun x => ofGibbs_chr G k i j x

lemma ofGibbs_riem (i j k l : Fin d) (x : Rd d) : (ofGibbs G).riem i j k l x = 0 := by
  unfold riem
  simp [ofGibbs_chr_fun, pderiv_const, ofGibbs_chr]

lemma ofGibbs_ricci (i j : Fin d) (x : Rd d) : (ofGibbs G).ricci i j x = 0 := by
  unfold ricci
  simp [ofGibbs_riem]

lemma ofGibbs_hess (u : Rd d → ℝ) (i j : Fin d) (x : Rd d) :
    (ofGibbs G).hess u i j x = pderiv (pderiv u j) i x := by
  unfold hess
  simp [ofGibbs_chr]

/-- **Consistency with (1.16.5)**: for the flat co-metric `δ`, the Riemannian Bochner formula is the Euclidean one,
`Γ₂(f) = Σ_{ij} (∂_i∂_j f)² + Σ_{ij} ∂_i∂_jV ∂_if ∂_jf`, the right-hand side of `gibbsRd_Γ₂_eq`. -/
theorem ofGibbs_bochner {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) :
    (ofGibbs G).riemDiff.Γ₂ f f x = ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 +
      ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x := by
  rw [(ofGibbs G).riem_bochner hf x]
  have hg : ∀ i j, (ofGibbs G).g i j x = if i = j then 1 else 0 := fun i j => rfl
  have e1 : ∑ i, ∑ j, ∑ k, ∑ l, (ofGibbs G).g i k x * (ofGibbs G).g j l x *
      (ofGibbs G).hess f i j x * (ofGibbs G).hess f k l x = ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 := by
    simp only [hg, ofGibbs_hess, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    simp [sq]
  have e2 : ∑ i, ∑ j, (ofGibbs G).beRicci i j x * (ofGibbs G).grad f i x * (ofGibbs G).grad f j x =
      ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x := by
    have hgr : ∀ i, (ofGibbs G).grad f i x = pderiv f i x := by
      intro i
      unfold grad
      simp [hg]
    have hW : (ofGibbs G).W = G.V := rfl
    simp only [hgr, beRicci, ofGibbs_ricci, zero_add, ofGibbs_hess, hW]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]

end flat

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
