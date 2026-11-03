import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Ell

/-!
# Change of variables for `Γ` and `L` of a weighted elliptic operator on `ℝ^d` (BGL (3.1.2), (3.1.8))

For `E : EllData d`, smooth `ψ : ℝᵏ → ℝ` and `C^∞` `f₁,…,f_k`:
`Γ(ψ(f),g) = Σᵢ ∂ᵢψ(f) Γ(fᵢ,g)`  (`Γ_comp`) and
`L(ψ(f)) = Σᵢ ∂ᵢψ(f) L fᵢ + Σᵢⱼ ∂ⱼ∂ᵢψ(f) Γ(fᵢ,fⱼ)`  (`L_comp`), plus the Leibniz rule `L(fg) = fLg + gLf + 2Γ(f,g)`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂)

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

lemma Pinv {f : Rd d → ℝ} (i : Fin d) (x : Rd d) :
    (E.w x)⁻¹ * E.P f i x = ∑ j, E.a i j x * pderiv f j x := by
  unfold P
  have := (E.w_pos x).ne'
  field_simp

/-- Leibniz rule `P(fg)ᵢ = g Pᵢ(f) + f Pᵢ(g)`. -/
lemma P_mul {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (i : Fin d) :
    E.P (f * g) i = g * E.P f i + f * E.P g i := by
  funext y
  simp only [P, Pi.add_apply, Pi.mul_apply]
  have h : ∀ j, pderiv (f * g) j y = pderiv f j y * g y + f y * pderiv g j y := fun j =>
    pderiv_mul hf hg j y
  simp only [h, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Leibniz rule** `L(fg) = f L g + g L f + 2 Γ(f,g)`. -/
theorem L_mul {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (x : Rd d) :
    E.L (f * g) x = f x * E.L g x + g x * E.L f x + 2 * E.Γ f g x := by
  have hL : E.L (f * g) x = (E.w x)⁻¹ * ∑ i, pderiv (E.P (f * g) i) i x := rfl
  rw [hL]
  simp only [E.P_mul hf hg]
  have hs : ∀ i, pderiv (g * E.P f i + f * E.P g i) i x =
      pderiv g i x * E.P f i x + g x * pderiv (E.P f i) i x +
        (pderiv f i x * E.P g i x + f x * pderiv (E.P g i) i x) := by
    intro i
    rw [pderiv_add (show Sm (g * E.P f i) from hg.mul (E.sm_P hf i))
      (show Sm (f * E.P g i) from hf.mul (E.sm_P hg i)),
      pderiv_mul hg (E.sm_P hf i), pderiv_mul hf (E.sm_P hg i)]
  simp only [hs, Finset.sum_add_distrib, mul_add]
  have e1 : (E.w x)⁻¹ * ∑ i, g x * pderiv (E.P f i) i x = g x * E.L f x := by
    rw [L_eq, ← Finset.mul_sum]; ring
  have e2 : (E.w x)⁻¹ * ∑ i, f x * pderiv (E.P g i) i x = f x * E.L g x := by
    rw [L_eq, ← Finset.mul_sum]; ring
  have e3 : (E.w x)⁻¹ * ∑ i, pderiv g i x * E.P f i x = E.Γ g f x := by
    rw [Finset.mul_sum]
    unfold Γ
    refine Finset.sum_congr rfl fun i _ => ?_
    have := E.Pinv (f := f) i x
    calc (E.w x)⁻¹ * (pderiv g i x * E.P f i x)
        = pderiv g i x * ((E.w x)⁻¹ * E.P f i x) := by ring
      _ = _ := by rw [this, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e4 : (E.w x)⁻¹ * ∑ i, pderiv f i x * E.P g i x = E.Γ f g x := by
    rw [Finset.mul_sum]
    unfold Γ
    refine Finset.sum_congr rfl fun i _ => ?_
    have := E.Pinv (f := g) i x
    calc (E.w x)⁻¹ * (pderiv f i x * E.P g i x)
        = pderiv f i x * ((E.w x)⁻¹ * E.P g i x) := by ring
      _ = _ := by rw [this, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e5 : E.Γ g f x = E.Γ f g x := congrFun (E.Γ_symm g f) x
  rw [e3, e4, e1, e2, e5]
  ring

/-- the coordinate carré du champ is the one defined from `L` by `½(L(fg) − fLg − gLf)` (Def. 3.3.1 (iv)) -/
theorem ΓA_formula {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (x : Rd d) :
    (E.L (f * g) x - f x * E.L g x - g x * E.L f x) / 2 = E.Γ f g x := by
  rw [E.L_mul hf hg x]; ring

/-- **Change of variables for `Γ`** (BGL (3.1.2)/(3.4.1)) on `C^∞`. -/
theorem Γ_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (F : Fin k → Rd d → ℝ) (hF : ∀ i, Sm (F i)) (g : Rd d → ℝ) (x : Rd d) :
    E.Γ (fun y => ψ (fun i => F i y)) g x =
      ∑ l, pderiv ψ l (fun j => F j x) * E.Γ (F l) g x := by
  unfold Γ
  have h : ∀ i, pderiv (fun y => ψ (fun j => F j y)) i x =
      ∑ l, pderiv ψ l (fun j => F j x) * pderiv (F l) i x := fun i => pderiv_comp ψ hψ F hF i x
  simp only [h, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- **Change of variables for `L`** (BGL (3.1.8)) on `C^∞`. -/
theorem L_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (F : Fin k → Rd d → ℝ) (hF : ∀ i, Sm (F i)) (x : Rd d) :
    E.L (fun y => ψ (fun i => F i y)) x =
      ∑ i, pderiv ψ i (fun j => F j x) * E.L (F i) x +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => F l x) * E.Γ (F i) (F j) x := by
  set Φ : Rd d → ℝ := fun y => ψ (fun i => F i y) with hΦ
  have hψk : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (pderiv ψ l) := fun l =>
    MarkovTriple.Sanity.OU.contDiff_pderiv ψ hψ l
  have hcl : ∀ l, Sm (fun y => pderiv ψ l (fun j => F j y)) := fun l => sm_comp k _ (hψk l) F hF
  have hPΦ : ∀ i, E.P Φ i = fun y => ∑ l, pderiv ψ l (fun j => F j y) * E.P (F l) i y := by
    intro i
    funext y
    have h : ∀ j, pderiv Φ j y = ∑ l, pderiv ψ l (fun j => F j y) * pderiv (F l) j y :=
      fun j => pderiv_comp ψ hψ F hF j y
    simp only [P, h, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
  have hD : ∀ i, pderiv (E.P Φ i) i x =
      ∑ l, ((∑ m, pderiv₂ ψ l m (fun j => F j x) * pderiv (F m) i x) * E.P (F l) i x +
        pderiv ψ l (fun j => F j x) * pderiv (E.P (F l) i) i x) := by
    intro i
    rw [hPΦ i, pderiv_sum _ (fun l => (hcl l).mul (E.sm_P (hF l) i))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pderiv_mul' (hcl l) (E.sm_P (hF l) i), pderiv_comp (pderiv ψ l) (hψk l) F hF i x]
    rfl
  have hLΦ : E.L Φ x = (E.w x)⁻¹ * ∑ i, ∑ l, ((∑ m, pderiv₂ ψ l m (fun j => F j x) * pderiv (F m) i x) *
      E.P (F l) i x + pderiv ψ l (fun j => F j x) * pderiv (E.P (F l) i) i x) := by
    rw [L_eq]; simp only [hD]
  have key : ∀ l, (E.w x)⁻¹ * ∑ i, ((∑ m, pderiv₂ ψ l m (fun j => F j x) * pderiv (F m) i x) *
      E.P (F l) i x + pderiv ψ l (fun j => F j x) * pderiv (E.P (F l) i) i x) =
      pderiv ψ l (fun j => F j x) * E.L (F l) x +
        ∑ m, pderiv₂ ψ l m (fun j => F j x) * E.Γ (F l) (F m) x := by
    intro l
    have e1 : ∀ i, (E.w x)⁻¹ * ((∑ m, pderiv₂ ψ l m (fun j => F j x) * pderiv (F m) i x) *
        E.P (F l) i x + pderiv ψ l (fun j => F j x) * pderiv (E.P (F l) i) i x) =
        (∑ m, pderiv₂ ψ l m (fun j => F j x) * pderiv (F m) i x) *
          (∑ j, E.a i j x * pderiv (F l) j x) +
        pderiv ψ l (fun j => F j x) * ((E.w x)⁻¹ * pderiv (E.P (F l) i) i x) := by
      intro i
      rw [← E.Pinv (f := F l) i x]; ring
    rw [Finset.mul_sum]
    simp only [e1, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [L_eq, ← Finset.mul_sum, ← Finset.mul_sum]
    · have hs : ∀ m, E.Γ (F l) (F m) x = E.Γ (F m) (F l) x := fun m => congrFun (E.Γ_symm _ _) x
      rw [show (∑ m, pderiv₂ ψ l m (fun j => F j x) * E.Γ (F l) (F m) x) =
          ∑ m, pderiv₂ ψ l m (fun j => F j x) * E.Γ (F m) (F l) x from
        Finset.sum_congr rfl fun m _ => by rw [hs m]]
      simp only [Γ]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      conv_lhs => enter [2, i]; rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [hLΦ]
  rw [Finset.sum_comm (f := fun i l => ((∑ m, pderiv₂ ψ l m (fun j => F j x) * pderiv (F m) i x) *
      E.P (F l) i x + pderiv ψ l (fun j => F j x) * pderiv (E.P (F l) i) i x)), Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
