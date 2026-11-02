import Mathlib
import MarkovTriple.BGL.Instances.OU.Diffusion

/-!
# Gibbs measures `e^{-V} dx` on `ℝ`: pointwise calculus of `L f = f'' - V' f'`

Generalises `MarkovTriple.Sanity.OU` (`V = x²/2`).  `Γ f g = f' g'` is `Go`.  Everything here is
measure-free: the change-of-variables formulas for `Lg`, and the Bochner identity
`Γ₂(f) = f''² + V'' f'²` (`Gibbs.Γ₂_eq`), which gives `Γ₂ ≥ ρ Γ` as soon as `V'' ≥ ρ`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.Sanity.OU hiding A₀

namespace MarkovTriple.BGL.Instances.Gibbs

/-- the Gibbs generator `L f = f'' - V' f'`. -/
noncomputable def Lg (V : ℝ → ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => deriv (deriv f) x - deriv V x * deriv f x

section Calc
variable {V f g : ℝ → ℝ}

lemma Lg_mul (hf : Sm f) (hg : Sm g) (x : ℝ) :
    Lg V (f * g) x = Lg V f x * g x + 2 * (deriv f x * deriv g x) + f x * Lg V g x := by
  unfold Lg
  rw [deriv_mul_s hf hg, deriv_add_s (show Sm (deriv f * g) from hf.deriv'.mul hg)
    (show Sm (f * deriv g) from hf.mul hg.deriv'),
    deriv_mul_s hf.deriv' hg, deriv_mul_s hf hg.deriv']
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

lemma sm_Lg (hV : Sm V) (hf : Sm f) : Sm (Lg V f) := by
  unfold Lg
  exact hf.deriv'.deriv'.sub (hV.deriv'.mul hf.deriv')

lemma diffusion_g (V : ℝ → ℝ) (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, Sm (f i)) :
    Lg V (fun x => ψ (fun i => f i x)) =
        fun x => ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * Lg V (f i) x +
          ∑ i, ∑ j, MarkovTriple.BGL.pderiv₂ ψ i j (fun l => f l x) * Go (f i) (f j) x := by
  have hD := deriv_comp1 ψ hψ f hf
  funext x
  unfold Lg
  rw [hD]
  have hi : ∀ i, HasDerivAt (fun u : ℝ => MarkovTriple.BGL.pderiv ψ i (fun j => f j u) * deriv (f i) u)
      ((∑ j, MarkovTriple.BGL.pderiv (MarkovTriple.BGL.pderiv ψ i) j (fun l => f l x) * deriv (f j) x)
          * deriv (f i) x + MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * deriv (deriv (f i)) x) x := by
    intro i
    have h1 := hasDerivAt_comp1 (MarkovTriple.BGL.pderiv ψ i) (contDiff_pderiv ψ hψ i) f
      (fun j => deriv (f j) x) x (fun j => (hf j).hasDerivAt x)
    have h2 := (hf i).deriv'.hasDerivAt x
    exact h1.mul h2
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have h3 := hsum.deriv
  simp only at h3
  rw [h3]
  simp only [MarkovTriple.BGL.pderiv₂, Go, Finset.sum_add_distrib, Finset.sum_mul]
  have : ∀ i j, MarkovTriple.BGL.pderiv (MarkovTriple.BGL.pderiv ψ i) j =
      fun z => fderiv ℝ (fun y => MarkovTriple.BGL.pderiv ψ i y) z (Pi.single j 1) := fun i j => rfl
  simp only [this]
  have hs : ∑ i, ∑ j, (fderiv ℝ (fun y => MarkovTriple.BGL.pderiv ψ i y) (fun l => f l x))
        (Pi.single j 1) * deriv (f j) x * deriv (f i) x =
      ∑ i, ∑ j, (fderiv ℝ (fun y => MarkovTriple.BGL.pderiv ψ i y) (fun l => f l x))
        (Pi.single j 1) * (deriv (f i) x * deriv (f j) x) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e4 : ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * (deriv (deriv (f i)) x - deriv V x * deriv (f i) x)
      = ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * deriv (deriv (f i)) x
        - deriv V x * ∑ i, MarkovTriple.BGL.pderiv ψ i (fun j => f j x) * deriv (f i) x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e4, hs]
  ring

/-- **Bochner identity**: `Γ₂(f) = ½ (L Γ(f) − 2 Γ(f, L f)) = f''² + V'' f'²`. -/
theorem Γ₂_eq (hV : Sm V) (hf : Sm f) (x : ℝ) :
    (Lg V (Go f f) x - 2 * Go f (Lg V f) x) / 2 = deriv (deriv f) x ^ 2 + deriv (deriv V) x * deriv f x ^ 2 := by
  have hdd : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) y) y := fun y => hf.deriv'.hasDerivAt y
  have hddd : ∀ y, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) y) y :=
    fun y => hf.deriv'.deriv'.hasDerivAt y
  have hVd : ∀ y, HasDerivAt (deriv V) (deriv (deriv V) y) y := fun y => hV.deriv'.hasDerivAt y
  have hF : ∀ y, HasDerivAt (Go f f)
      (deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y) y := fun y =>
    (hdd y).mul (hdd y)
  have h1 : deriv (Go f f) = fun y =>
      deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y :=
    funext fun y => (hF y).deriv
  have hF2 : HasDerivAt (deriv (Go f f))
      (deriv (deriv (deriv f)) x * deriv f x + deriv (deriv f) x * deriv (deriv f) x +
        (deriv (deriv f) x * deriv (deriv f) x + deriv f x * deriv (deriv (deriv f)) x)) x := by
    rw [h1]
    exact ((hddd x).mul (hdd x)).add ((hdd x).mul (hddd x))
  have hL : HasDerivAt (Lg V f)
      (deriv (deriv (deriv f)) x - (deriv (deriv V) x * deriv f x + deriv V x * deriv (deriv f) x)) x := by
    unfold Lg
    exact (hddd x).sub ((hVd x).mul (hdd x))
  have e1 : Lg V (Go f f) x = deriv (deriv (Go f f)) x - deriv V x * deriv (Go f f) x := rfl
  have e2 : Go f (Lg V f) x = deriv f x * deriv (Lg V f) x := rfl
  rw [e1, e2, hF2.deriv, hL.deriv, h1]
  ring

/-- `Γ₂ ≥ ρ Γ` when `V'' ≥ ρ` (the Bakry–Émery criterion `CD(ρ,∞)`, pointwise on smooth functions). -/
theorem Γ₂_ge (hV : Sm V) {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv V) x) (hf : Sm f) (x : ℝ) :
    ρ * Go f f x ≤ (Lg V (Go f f) x - 2 * Go f (Lg V f) x) / 2 := by
  rw [Γ₂_eq hV hf x]
  have h1 : ρ * deriv f x ^ 2 ≤ deriv (deriv V) x * deriv f x ^ 2 :=
    mul_le_mul_of_nonneg_right (hρ x) (sq_nonneg _)
  simp only [Go]
  nlinarith [sq_nonneg (deriv (deriv f) x)]

end Calc

end MarkovTriple.BGL.Instances.Gibbs
