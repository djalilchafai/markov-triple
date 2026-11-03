import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Calculus

/-!
# Gibbs on `ℝ`: the cut-off commutator formulas for `L` and `L²` (R17, Stream A; measure-free)

For smooth `V`, `ψ`, `v`: `L(ψ v) − L v` and `L²(ψ v) − L² v` expanded in the jets of `ψ`, `v` and `V`
(BGL (1.11.2)-type product rule `L(fg) = f Lg + g Lf + 2Γ(f,g)`, applied three times).  The coefficients
`cc0 … cc4` are polynomials in `ψ', …, ψ⁗` and `V', V'', V'''`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.Sanity.OU hiding A₀

namespace MarkovTriple.BGL.Instances.Gibbs

section Calc
variable {V f g : ℝ → ℝ}

lemma Lg_add (hf : Sm f) (hg : Sm g) (x : ℝ) : Lg V (f + g) x = Lg V f x + Lg V g x := by
  unfold Lg
  rw [deriv_add_s hf hg, deriv_add_s hf.deriv' hg.deriv']
  simp only [Pi.add_apply]; ring

lemma Lg_smul (c : ℝ) (hf : Sm f) (x : ℝ) : Lg V (c • f) x = c * Lg V f x := by
  unfold Lg
  rw [deriv_smul_s c hf, deriv_smul_s c hf.deriv']
  simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma Lg_sub (hf : Sm f) (hg : Sm g) (x : ℝ) : Lg V (f - g) x = Lg V f x - Lg V g x := by
  have h1 : f - g = f + (-1 : ℝ) • g := by funext y; simp [sub_eq_add_neg]
  have hg' : Sm ((-1 : ℝ) • g) := hg.const_smul (-1 : ℝ)
  rw [h1, Lg_add hf hg', Lg_smul _ hg]; ring

/-- `(L f)' = f''' − V'' f' − V' f''`. -/
lemma deriv_Lg_jet (hV : Sm V) (hf : Sm f) (x : ℝ) :
    deriv (Lg V f) x = deriv (deriv (deriv f)) x -
      (deriv (deriv V) x * deriv f x + deriv V x * deriv (deriv f) x) := by
  have hL : HasDerivAt (Lg V f)
      (deriv (deriv (deriv f)) x - (deriv (deriv V) x * deriv f x + deriv V x * deriv (deriv f) x)) x := by
    unfold Lg
    exact (hf.deriv'.deriv'.hasDerivAt x).sub ((hV.deriv'.hasDerivAt x).mul (hf.deriv'.hasDerivAt x))
  exact hL.deriv

/-- `L L f` in jets. -/
lemma LL_jet (hV : Sm V) (hf : Sm f) (x : ℝ) :
    Lg V (Lg V f) x = deriv (deriv (deriv (deriv f))) x -
      (deriv (deriv (deriv V)) x * deriv f x + 2 * (deriv (deriv V) x * deriv (deriv f) x) +
        deriv V x * deriv (deriv (deriv f)) x) -
      deriv V x * (deriv (deriv (deriv f)) x -
        (deriv (deriv V) x * deriv f x + deriv V x * deriv (deriv f) x)) := by
  have e : deriv (Lg V f) = fun y => deriv (deriv (deriv f)) y -
      (deriv (deriv V) y * deriv f y + deriv V y * deriv (deriv f) y) := funext (deriv_Lg_jet hV hf)
  have h2 : HasDerivAt (deriv (Lg V f))
      (deriv (deriv (deriv (deriv f))) x -
        (deriv (deriv (deriv V)) x * deriv f x + deriv (deriv V) x * deriv (deriv f) x +
          (deriv (deriv V) x * deriv (deriv f) x + deriv V x * deriv (deriv (deriv f)) x))) x := by
    rw [e]
    exact (hf.deriv'.deriv'.deriv'.hasDerivAt x).sub
      (((hV.deriv'.deriv'.hasDerivAt x).mul (hf.deriv'.hasDerivAt x)).add
        ((hV.deriv'.hasDerivAt x).mul (hf.deriv'.deriv'.hasDerivAt x)))
  show deriv (deriv (Lg V f)) x - deriv V x * deriv (Lg V f) x = _
  rw [h2.deriv, deriv_Lg_jet hV hf x]
  ring

/-- coefficient of `v` in `L²(ψ v)`: `L²ψ`. -/
noncomputable def cc0 (V ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv (deriv (deriv ψ))) x -
      (deriv (deriv (deriv V)) x * deriv ψ x + 2 * (deriv (deriv V) x * deriv (deriv ψ) x) +
        deriv V x * deriv (deriv (deriv ψ)) x) -
      deriv V x * (deriv (deriv (deriv ψ)) x -
        (deriv (deriv V) x * deriv ψ x + deriv V x * deriv (deriv ψ) x))

/-- coefficient of `v'`. -/
noncomputable def cc1 (V ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * (deriv (deriv (deriv ψ)) x - (deriv (deriv V) x * deriv ψ x + deriv V x * deriv (deriv ψ) x)) +
    2 * (deriv (deriv (deriv ψ)) x - deriv V x * deriv (deriv ψ) x) - 2 * deriv ψ x * deriv (deriv V) x

/-- coefficient of `v''`. -/
noncomputable def cc2 (V ψ : ℝ → ℝ) (x : ℝ) : ℝ := 4 * deriv (deriv ψ) x - 4 * deriv ψ x * deriv V x

/-- coefficient of `v'''`. -/
noncomputable def cc3 (ψ : ℝ → ℝ) (x : ℝ) : ℝ := 4 * deriv ψ x

/-- coefficient of `L v`. -/
noncomputable def cc4 (V ψ : ℝ → ℝ) (x : ℝ) : ℝ := 2 * Lg V ψ x

/-- **commutator of `L` with a cut-off**: `L(ψ v) − L v = (ψ − 1) L v + (Lψ) v + 2ψ' v'`. -/
lemma L_mul_expand (hψ : Sm f) (hv : Sm g) (x : ℝ) :
    Lg V (f * g) x - Lg V g x = (f x - 1) * Lg V g x + Lg V f x * g x + 2 * deriv f x * deriv g x := by
  rw [Lg_mul hψ hv]; ring

/-- **commutator of `L²` with a cut-off**. -/
lemma LL_mul_expand (hV : Sm V) (hψ : Sm f) (hv : Sm g) (x : ℝ) :
    Lg V (Lg V (f * g)) x - Lg V (Lg V g) x = (f x - 1) * Lg V (Lg V g) x + cc0 V f x * g x +
      cc1 V f x * deriv g x + cc2 V f x * deriv (deriv g) x + cc3 f x * deriv (deriv (deriv g)) x +
      cc4 V f x * Lg V g x := by
  have hLψ : Sm (Lg V f) := sm_Lg hV hψ
  have hLv : Sm (Lg V g) := sm_Lg hV hv
  have e1 : Lg V (f * g) = Lg V f * g + (2 : ℝ) • (deriv f * deriv g) + f * Lg V g := by
    funext y
    rw [Lg_mul hψ hv y]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hA : Sm (Lg V f * g) := hLψ.mul hv
  have hBB : Sm (deriv f * deriv g) := hψ.deriv'.mul hv.deriv'
  have hB : Sm ((2 : ℝ) • (deriv f * deriv g)) := hBB.const_smul (2 : ℝ)
  have hC : Sm (f * Lg V g) := hψ.mul hLv
  have hAB : Sm (Lg V f * g + (2 : ℝ) • (deriv f * deriv g)) := hA.add hB
  rw [e1, Lg_add hAB hC, Lg_add hA hB, Lg_smul 2 hBB,
    Lg_mul hLψ hv, Lg_mul hψ.deriv' hv.deriv', Lg_mul hψ hLv, deriv_Lg_jet hV hψ x,
    deriv_Lg_jet hV hv x, LL_jet hV hψ x]
  simp only [cc0, cc1, cc2, cc3, cc4, Lg]
  ring

end Calc

end MarkovTriple.BGL.Instances.Gibbs
