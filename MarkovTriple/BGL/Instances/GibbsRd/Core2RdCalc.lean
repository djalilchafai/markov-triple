import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Bochner

/-!
# Pointwise calculus for the `ℝ^d` `Core2` cut-off argument (R18, Stream A3, target B1)

Statements: `STATEMENTS_R18_Core2Rd.md` (B1).  `Lr_mul` (Leibniz), `Lr_Gr` (polarised Bochner commutation
`L Γ(f,g) = Γ(Lf,g) + Γ(f,Lg) + 2 Σ f_ij g_ij + 2 Σ V_ij f_i g_j`), `Lr_remainder`.
-/

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ} {V f g : Rd d → ℝ}

lemma sm_Gr' (hf : Sm f) (hg : Sm g) : Sm (Gr f g) :=
  ContDiff.sum fun k _ => (hf.pderiv k).mul (hg.pderiv k)

/-- `∂ₖ(L f)` for any smooth potential. -/
lemma pderiv_Lr' (hV : Sm V) (hf : Sm f) (k : Fin d) (x : Rd d) :
    pderiv (Lr V f) k x = ∑ j, (pderiv (pderiv (pderiv f j) j) k x -
      (pderiv (pderiv V j) k x * pderiv f j x + pderiv V j x * pderiv (pderiv f j) k x)) := by
  unfold Lr
  rw [pderiv_sum _ (fun j => ((hf.pderiv j).pderiv j).sub ((hV.pderiv j).mul (hf.pderiv j))) k x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_sub' ((hf.pderiv j).pderiv j) ((hV.pderiv j).mul (hf.pderiv j)) k x,
    pderiv_mul' (hV.pderiv j) (hf.pderiv j) k x]

/-- Leibniz rule `L(fg) = f Lg + g Lf + 2Γ(f,g)`. -/
theorem Lr_mul (hf : Sm f) (hg : Sm g) (x : Rd d) :
    Lr V (f * g) x = f x * Lr V g x + g x * Lr V f x + 2 * Gr f g x := by
  have h2 : ∀ i, pderiv (pderiv (f * g) i) i x =
      pderiv (pderiv f i) i x * g x + pderiv f i x * pderiv g i x +
        (pderiv f i x * pderiv g i x + f x * pderiv (pderiv g i) i x) := by
    intro i
    have h1 : pderiv (f * g) i = fun y => pderiv f i y * g y + f y * pderiv g i y :=
      funext (pderiv_mul hf hg i)
    rw [h1, pderiv_add' ((hf.pderiv i).mul hg) (hf.mul (hg.pderiv i)) i x,
      pderiv_mul' (hf.pderiv i) hg i x, pderiv_mul' hf (hg.pderiv i) i x]
  unfold Lr Gr
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i, pderiv_mul hf hg i x]
  ring

lemma Lr_add_smul (hf : Sm f) (hg : Sm g) (c : ℝ) (x : Rd d) :
    Lr V (fun y => f y + c * g y) x = Lr V f x + c * Lr V g x := by
  have h1 : ∀ i, pderiv (fun y => f y + c * g y) i = fun y => pderiv f i y + c * pderiv g i y := by
    intro i; funext y
    rw [pderiv_add' hf (contDiff_const.mul hg) i y,
      pderiv_mul' contDiff_const hg i y, pderiv_const]
    ring
  have h2 : ∀ i, pderiv (pderiv (fun y => f y + c * g y) i) i x =
      pderiv (pderiv f i) i x + c * pderiv (pderiv g i) i x := by
    intro i
    rw [h1 i, pderiv_add' (hf.pderiv i) (contDiff_const.mul (hg.pderiv i)) i x,
      pderiv_mul' contDiff_const (hg.pderiv i) i x, pderiv_const]
    ring
  unfold Lr
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i, congrFun (h1 i) x]
  ring

/-- algebraic core of `Lr_Gr`. -/
lemma alg_LrGr {n : ℕ} (fd gd Vd : Fin n → ℝ) (Hf Hg HV Tf Tg : Fin n → Fin n → ℝ)
    (hHf : ∀ i j, Hf i j = Hf j i) (hHg : ∀ i j, Hg i j = Hg j i) (hHV : ∀ i j, HV i j = HV j i) :
    ∑ i, ((∑ k, ((Tf k i * gd k + Hf k i * Hg k i) + (Hf k i * Hg k i + fd k * Tg k i))) -
        Vd i * ∑ k, (Hf k i * gd k + fd k * Hg k i)) =
      ∑ k, ((∑ j, (Tf k j - (HV j k * fd j + Vd j * Hf j k))) * gd k) +
      ∑ k, fd k * ∑ j, (Tg k j - (HV j k * gd j + Vd j * Hg j k)) +
      2 * ∑ i, ∑ j, Hf i j * Hg i j + 2 * ∑ i, ∑ j, HV i j * fd i * gd j := by
  have e1 : ∑ i, ∑ k, Tf k i * gd k = ∑ k, ∑ j, Tf k j * gd k := Finset.sum_comm
  have e2 : ∑ i, ∑ k, fd k * Tg k i = ∑ k, ∑ j, fd k * Tg k j := Finset.sum_comm
  have e3 : ∑ i, ∑ k, Hf k i * Hg k i = ∑ i, ∑ j, Hf i j * Hg i j := Finset.sum_comm
  have e4 : ∑ i, ∑ k, Vd i * (Hf k i * gd k) = ∑ k, ∑ j, Vd j * Hf j k * gd k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hHf k j]; ring
  have e5 : ∑ i, ∑ k, Vd i * (fd k * Hg k i) = ∑ k, ∑ j, fd k * (Vd j * Hg j k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hHg k j]; ring
  have e6 : ∑ i, ∑ j, HV i j * fd i * gd j = ∑ k, ∑ j, HV j k * fd j * gd k := Finset.sum_comm
  have e7 : ∑ i, ∑ j, HV i j * fd i * gd j = ∑ k, ∑ j, fd k * (HV j k * gd j) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hHV k j]; ring
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, mul_sub, add_mul, sub_mul] at *
  have e8 : ∑ x, ∑ i, 2 * (Hf x i * Hg x i) = 2 * ∑ i, ∑ j, Hf i j * Hg i j := by
    simp only [Finset.mul_sum]
  have e9 : ∑ x, ∑ i, 2 * (HV x i * fd x * gd i) = 2 * ∑ i, ∑ j, HV i j * fd i * gd j := by
    simp only [Finset.mul_sum]
  linarith

/-- Polarised Bochner commutation `L Γ(f,g) = Γ(Lf,g) + Γ(f,Lg) + 2 Σ f_ij g_ij + 2 Σ V_ij f_i g_j`. -/
theorem Lr_Gr (hV : Sm V) (hf : Sm f) (hg : Sm g) (x : Rd d) :
    Lr V (Gr f g) x = Gr (Lr V f) g x + Gr f (Lr V g) x +
      2 * ∑ i, ∑ j, pderiv (pderiv f i) j x * pderiv (pderiv g i) j x +
      2 * ∑ i, ∑ j, pderiv (pderiv V i) j x * pderiv f i x * pderiv g j x := by
  have hGi : ∀ i, pderiv (Gr f g) i = fun y => ∑ k, (pderiv (pderiv f k) i y * pderiv g k y +
      pderiv f k y * pderiv (pderiv g k) i y) := by
    intro i; funext y
    unfold Gr
    rw [pderiv_sum _ (fun k => (hf.pderiv k).mul (hg.pderiv k)) i y]
    exact Finset.sum_congr rfl fun k _ => pderiv_mul' (hf.pderiv k) (hg.pderiv k) i y
  have hGii : ∀ i, pderiv (pderiv (Gr f g) i) i x = ∑ k, ((pderiv (pderiv (pderiv f k) i) i x *
      pderiv g k x + pderiv (pderiv f k) i x * pderiv (pderiv g k) i x) +
      (pderiv (pderiv f k) i x * pderiv (pderiv g k) i x +
        pderiv f k x * pderiv (pderiv (pderiv g k) i) i x)) := by
    intro i
    rw [hGi i, pderiv_sum _ (fun k => (((hf.pderiv k).pderiv i).mul (hg.pderiv k)).add
      ((hf.pderiv k).mul ((hg.pderiv k).pderiv i))) i x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pderiv_add' (((hf.pderiv k).pderiv i).mul (hg.pderiv k))
      ((hf.pderiv k).mul ((hg.pderiv k).pderiv i)) i x,
      pderiv_mul' ((hf.pderiv k).pderiv i) (hg.pderiv k) i x,
      pderiv_mul' (hf.pderiv k) ((hg.pderiv k).pderiv i) i x]
  have hL : ∀ (u : Rd d → ℝ), Sm u → ∀ k, pderiv (Lr V u) k x = ∑ j, (pderiv (pderiv (pderiv u k) j) j x -
      (pderiv (pderiv V j) k x * pderiv u j x + pderiv V j x * pderiv (pderiv u j) k x)) := by
    intro u hu k
    rw [pderiv_Lr' hV hu k x]
    exact Finset.sum_congr rfl fun j _ => by rw [third_symm hu j k x]
  have hLHS : Lr V (Gr f g) x = ∑ i, ((∑ k, ((pderiv (pderiv (pderiv f k) i) i x *
      pderiv g k x + pderiv (pderiv f k) i x * pderiv (pderiv g k) i x) +
      (pderiv (pderiv f k) i x * pderiv (pderiv g k) i x +
        pderiv f k x * pderiv (pderiv (pderiv g k) i) i x))) -
      pderiv V i x * ∑ k, (pderiv (pderiv f k) i x * pderiv g k x +
        pderiv f k x * pderiv (pderiv g k) i x)) := by
    unfold Lr
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGii i, congrFun (hGi i) x]
  have hA : Gr (Lr V f) g x = ∑ k, (∑ j, (pderiv (pderiv (pderiv f k) j) j x -
      (pderiv (pderiv V j) k x * pderiv f j x + pderiv V j x * pderiv (pderiv f j) k x))) *
        pderiv g k x := by
    unfold Gr
    exact Finset.sum_congr rfl fun k _ => by rw [hL f hf k]
  have hB : Gr f (Lr V g) x = ∑ k, pderiv f k x * ∑ j, (pderiv (pderiv (pderiv g k) j) j x -
      (pderiv (pderiv V j) k x * pderiv g j x + pderiv V j x * pderiv (pderiv g j) k x)) := by
    unfold Gr
    exact Finset.sum_congr rfl fun k _ => by rw [hL g hg k]
  rw [hLHS, hA, hB]
  exact alg_LrGr (fun k => pderiv f k x) (fun k => pderiv g k x) (fun k => pderiv V k x)
    (fun k i => pderiv (pderiv f k) i x) (fun k i => pderiv (pderiv g k) i x)
    (fun j k => pderiv (pderiv V j) k x)
    (fun k j => pderiv (pderiv (pderiv f k) j) j x) (fun k j => pderiv (pderiv (pderiv g k) j) j x)
    (fun i j => pderiv_symm hf i j x) (fun i j => pderiv_symm hg i j x)
    (fun i j => pderiv_symm hV i j x)

lemma Gr_comm (f g : Rd d → ℝ) (x : Rd d) : Gr f g x = Gr g f x := by
  unfold Gr
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The remainder formula of the `Core2` cut-off argument, `R = v · Lχ + 2 Γ(χ,v)`. -/
theorem Lr_remainder (hV : Sm V) {v χ : Rd d → ℝ} (hv : Sm v) (hχ : Sm χ) (x : Rd d) :
    Lr V (fun x => v x * Lr V χ x + 2 * Gr χ v x) x =
      Lr V v x * Lr V χ x + v x * Lr V (Lr V χ) x + 4 * Gr (Lr V χ) v x + 2 * Gr χ (Lr V v) x +
      4 * ∑ i, ∑ j, pderiv (pderiv χ i) j x * pderiv (pderiv v i) j x +
      4 * ∑ i, ∑ j, pderiv (pderiv V i) j x * pderiv χ i x * pderiv v j x := by
  have hP : Sm (Lr V χ) := sm_Lr hV hχ
  rw [Lr_add_smul (hv.mul hP) (sm_Gr' hχ hv) 2 x]
  have h1 := Lr_mul (V := V) hv hP x
  have h2 := Lr_Gr hV hχ hv x
  have h3 := Gr_comm v (Lr V χ) x
  rw [show (fun x => v x * Lr V χ x) = v * Lr V χ from rfl, h1, h2]
  linarith

end MarkovTriple.BGL.Instances.GibbsRd
