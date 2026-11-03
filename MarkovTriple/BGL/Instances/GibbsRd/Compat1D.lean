import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Main
import MarkovTriple.BGL.Instances.Gibbs.Calculus

/-!
# Consistency with the one-dimensional Gibbs development (`Instances/Gibbs`)

For `d = 1`, `Rd 1 = Fin 1 → ℝ ≅ ℝ` and the `ℝ^d` generator `Lr V` and carré du champ `Gr` restrict, along the diagonal
`t ↦ (t)`, to the one-dimensional `Lg Ṽ` and `Go` of `Gibbs/Calculus` (`Lg Ṽ f̃ = f̃'' − Ṽ' f̃'`, `Go f̃ g̃ = f̃' g̃'`).
This ties the new `GibbsRd` development to the already audited 1-D one.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

/-- the restriction of a function on `ℝ^1` to `ℝ` -/
def restr1 (f : Rd 1 → ℝ) : ℝ → ℝ := fun t => f (fun _ => t)

lemma hasDerivAt_restr1 {f : Rd 1 → ℝ} (hf : Sm f) (t : ℝ) :
    HasDerivAt (restr1 f) (pderiv f 0 (fun _ => t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (fun _ : Fin 1 => s)) (fun _ : Fin 1 => (1 : ℝ)) t :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id t
  have h2 := (hf.hasFDerivAt' (fun _ => t)).comp_hasDerivAt t h1
  have e : (fun _ : Fin 1 => (1 : ℝ)) = Pi.single 0 1 := by
    ext i; fin_cases i; simp
  refine h2.congr_deriv ?_
  rw [e]; rfl

lemma deriv_restr1 {f : Rd 1 → ℝ} (hf : Sm f) : deriv (restr1 f) = restr1 (pderiv f 0) :=
  funext fun t => (hasDerivAt_restr1 hf t).deriv

/-- `Γ` agrees with the 1-D `Go` -/
theorem Gr_restr1 {f g : Rd 1 → ℝ} (hf : Sm f) (hg : Sm g) (t : ℝ) :
    Gr f g (fun _ => t) = MarkovTriple.Sanity.OU.Go (restr1 f) (restr1 g) t := by
  simp only [Gr, MarkovTriple.Sanity.OU.Go, deriv_restr1 hf, deriv_restr1 hg, restr1, Fin.sum_univ_one]

/-- `Lr V` agrees with the 1-D Gibbs generator `Lg` -/
theorem Lr_restr1 {V f : Rd 1 → ℝ} (hV : Sm V) (hf : Sm f) (t : ℝ) :
    Lr V f (fun _ => t) = MarkovTriple.BGL.Instances.Gibbs.Lg (restr1 V) (restr1 f) t := by
  have h1 : deriv (restr1 f) = restr1 (pderiv f 0) := deriv_restr1 hf
  have h2 : deriv (deriv (restr1 f)) = restr1 (pderiv (pderiv f 0) 0) := by
    rw [h1]; exact deriv_restr1 (hf.pderiv 0)
  have h2' : deriv (deriv (restr1 f)) t = pderiv (pderiv f 0) 0 (fun _ => t) := by rw [h2]; rfl
  have h3 : deriv (restr1 V) t = pderiv V 0 (fun _ => t) := by rw [deriv_restr1 hV]; rfl
  have h4 : deriv (restr1 f) t = pderiv f 0 (fun _ => t) := by rw [h1]; rfl
  simp only [Lr, MarkovTriple.BGL.Instances.Gibbs.Lg, Fin.sum_univ_one]
  rw [h2', h3, h4]

end MarkovTriple.BGL.Instances.GibbsRd
