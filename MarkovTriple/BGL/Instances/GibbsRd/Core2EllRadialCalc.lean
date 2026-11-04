import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllCalc

/-!
# Chain rule for `L` and `Γ` with a one-variable outer function (R19, Stream A6, target T6)

For `E : EllData d`, `ψ` smooth and `φ : ℝ → ℝ` smooth:
`Γ(φ∘ψ, θ∘ψ) = φ'(ψ) θ'(ψ) Γ(ψ)` and `L(φ∘ψ) = φ'(ψ) Lψ + φ''(ψ) Γ(ψ)` (BGL (3.1.2), (3.1.8) with `k = 1`).
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv pderiv₂)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

/-- one-variable smoothness (`C^∞` in the `ℕ∞` sense) -/
abbrev S1 (f : ℝ → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

lemma S1.dsm {f : ℝ → ℝ} (hf : S1 f) : S1 (deriv f) :=
  (contDiff_infty_iff_deriv.1 hf).2

lemma S1.hasDerivAt {f : ℝ → ℝ} (hf : S1 f) (s : ℝ) : HasDerivAt f (deriv f s) s :=
  ((hf.differentiable (by simp)) s).hasDerivAt

lemma pderiv_comp1 {φ : ℝ → ℝ} {ψ : Rd d → ℝ} (hφ : S1 φ) (hψ : Sm ψ) (i : Fin d) (x : Rd d) :
    pderiv (fun y => φ (ψ y)) i x = deriv φ (ψ x) * pderiv ψ i x := by
  have h := (hφ.hasDerivAt (ψ x)).comp_hasFDerivAt x (hψ.hasFDerivAt' x)
  unfold pderiv
  rw [show (fun y => φ (ψ y)) = φ ∘ ψ from rfl, h.fderiv]
  simp

lemma sm_comp1 {φ : ℝ → ℝ} {ψ : Rd d → ℝ} (hφ : S1 φ) (hψ : Sm ψ) : Sm (fun y => φ (ψ y)) :=
  hφ.comp hψ

namespace EllData
variable (E : EllData d)

lemma Γ_comp1 {φ θ : ℝ → ℝ} {ψ : Rd d → ℝ} (hφ : S1 φ) (hθ : S1 θ) (hψ : Sm ψ) (x : Rd d) :
    E.Γ (fun y => φ (ψ y)) (fun y => θ (ψ y)) x = deriv φ (ψ x) * deriv θ (ψ x) * E.Γ ψ ψ x := by
  unfold Γ
  simp only [pderiv_comp1 hφ hψ, pderiv_comp1 hθ hψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma Γ_comp1_left {φ : ℝ → ℝ} {ψ : Rd d → ℝ} (hφ : S1 φ) (hψ : Sm ψ) (k : Rd d → ℝ) (x : Rd d) :
    E.Γ (fun y => φ (ψ y)) k x = deriv φ (ψ x) * E.Γ ψ k x := by
  unfold Γ
  simp only [pderiv_comp1 hφ hψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `L(φ∘ψ) = φ'(ψ) Lψ + φ''(ψ) Γ(ψ)`. -/
theorem L_comp1 {φ : ℝ → ℝ} {ψ : Rd d → ℝ} (hφ : S1 φ) (hψ : Sm ψ) (x : Rd d) :
    E.L (fun y => φ (ψ y)) x = deriv φ (ψ x) * E.L ψ x + deriv (deriv φ) (ψ x) * E.Γ ψ ψ x := by
  set φ' : (Fin 1 → ℝ) → ℝ := fun v => φ (v 0) with hφ'
  have hc : Sm (fun v : Rd 1 => v 0) := contDiff_apply ℝ ℝ (0 : Fin 1)
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ' := hφ.comp hc
  have h := E.L_comp φ' hφs (fun _ => ψ) (fun _ => hψ) x
  have e1 : ∀ v : Fin 1 → ℝ, MarkovTriple.BGL.pderiv φ' 0 v = deriv φ (v 0) := by
    intro v
    have := pderiv_comp1 (d := 1) (φ := φ) (ψ := fun v : Rd 1 => v 0) hφ hc 0 v
    simp only [hφ']
    rw [this, pderiv_coord]
    simp
  have e2 : ∀ v : Fin 1 → ℝ, pderiv₂ φ' 0 0 v = deriv (deriv φ) (v 0) := by
    intro v
    show fderiv ℝ (fun y => pderiv φ' 0 y) v (Pi.single 0 1) = _
    have : (fun y => pderiv φ' 0 y) = fun y : Rd 1 => deriv φ (y 0) := funext e1
    rw [this]
    have := pderiv_comp1 (d := 1) (φ := deriv φ) (ψ := fun v : Rd 1 => v 0) hφ.dsm hc 0 v
    unfold pderiv at this
    rw [this]
    have h3 := pderiv_coord (d := 1) 0 0 v
    unfold pderiv at h3
    rw [h3]; simp
  have hlhs : (fun y => φ' (fun i : Fin 1 => (fun _ => ψ) i y)) = fun y => φ (ψ y) := rfl
  rw [hlhs] at h
  rw [h]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, e1, e2]

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
