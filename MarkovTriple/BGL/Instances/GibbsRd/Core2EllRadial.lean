import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllRadialScalar
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllMain

/-!
# Radial exhaustions: a sufficient condition for `CoreCut` relative to `a_exh` (R19, Stream A6; target T6)

`RadialJets E ψ α β`: `ψ ≥ 0` smooth proper with `Lψ = α(ψ)`, `Γ(ψ) = β(ψ)` for one-variable smooth `α, β` satisfying the
scale-invariant growth conditions
`|α(s)| ≤ C(1+s)`, `0 ≤ β(s) ≤ C(1+s)²`, `|α'| ≤ C`, `|β'| ≤ C(1+s)`, `|α''|(1+s) ≤ C`, `|β''| ≤ C`   (`s ≥ 0`).
Then the cut-offs `χ_n = σ(ψ/(n+1))` form a `CutFamily` (`coreCut_of_radial`).  The `L,Γ,Γ₂` calculus reduces everything to the
one-variable operator `𝓛φ = αφ' + βφ''`: `Γ(φ∘ψ) = φ'²β`, `L(φ∘ψ) = (𝓛φ)∘ψ`, `Γ₂(φ∘ψ) = ½𝓛(φ'²β) - φ'(𝓛φ)'β`.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

/-- **Radial jets** of an exhaustion function (hypothesis of T6). -/
structure RadialJets (E : EllData d) (ψ : Rd d → ℝ) (α β : ℝ → ℝ) : Prop where
  smooth : Sm ψ
  nonneg : ∀ x, 0 ≤ ψ x
  proper : ∀ c : ℝ, Bornology.IsBounded {x : Rd d | ψ x ≤ c}
  α_smooth : S1 α
  β_smooth : S1 β
  L_eq : ∀ x, E.L ψ x = α (ψ x)
  Γ_eq : ∀ x, E.Γ ψ ψ x = β (ψ x)
  growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → |α s| ≤ C * (1 + s) ∧ 0 ≤ β s ∧ β s ≤ C * (1 + s) ^ 2 ∧
    |deriv α s| ≤ C ∧ |deriv β s| ≤ C * (1 + s) ∧ |deriv (deriv α) s| * (1 + s) ≤ C ∧
    |deriv (deriv β) s| ≤ C

/-- the hypothesis class T6 -/
def EllData.RadialExh (E : EllData d) : Prop := ∃ (ψ : Rd d → ℝ) (α β : ℝ → ℝ), RadialJets E ψ α β

/-! ### the scalar quantities -/

/-- `P₁' = (φ'α + φ''β)'` -/
def qP1' (f1 f2 f3 a a1 b b1 : ℝ) : ℝ := f2 * a + f1 * a1 + (f3 * b + f2 * b1)

/-- `P₁'' = (φ'α + φ''β)''` -/
def qP1'' (f1 f2 f3 f4 a a1 a2 b b1 b2 : ℝ) : ℝ :=
  (f3 * a + f2 * a1 + (f2 * a1 + f1 * a2)) + ((f4 * b + f3 * b1) + (f3 * b1 + f2 * b2))

/-- `Θ' = (φ'² β)'` -/
def qΘ' (f1 f2 b b1 : ℝ) : ℝ := (f2 * f1 + f1 * f2) * b + f1 * f1 * b1

/-- `Θ'' = (φ'² β)''` -/
def qΘ'' (f1 f2 f3 b b1 b2 : ℝ) : ℝ :=
  ((f3 * f1 + f2 * f2) + (f2 * f2 + f1 * f3)) * b + (f2 * f1 + f1 * f2) * b1 +
    ((f2 * f1 + f1 * f2) * b1 + f1 * f1 * b2)

namespace EllData
variable (E : EllData d)

/-- **the five cut-off quantities as one-variable expressions**. -/
theorem radial_identities {ψ : Rd d → ℝ} {α β : ℝ → ℝ} (hJ : RadialJets E ψ α β) {φ : ℝ → ℝ} (hφ : S1 φ)
    (x : Rd d) (s f1 f2 f3 f4 a a1 a2 b b1 b2 : ℝ) (hs : s = ψ x) (h1 : f1 = deriv φ s)
    (h2 : f2 = deriv (deriv φ) s) (h3 : f3 = deriv (deriv (deriv φ)) s)
    (h4 : f4 = deriv (deriv (deriv (deriv φ))) s) (ha : a = α s) (ha1 : a1 = deriv α s)
    (ha2 : a2 = deriv (deriv α) s) (hb : b = β s) (hb1 : b1 = deriv β s) (hb2 : b2 = deriv (deriv β) s) :
    E.Γ (fun y => φ (ψ y)) (fun y => φ (ψ y)) x = f1 * f1 * b ∧
    E.L (fun y => φ (ψ y)) x = f1 * a + f2 * b ∧
    E.L (E.L (fun y => φ (ψ y))) x = qP1' f1 f2 f3 a a1 b b1 * a + qP1'' f1 f2 f3 f4 a a1 a2 b b1 b2 * b ∧
    E.Γ (E.L (fun y => φ (ψ y))) (E.L (fun y => φ (ψ y))) x =
      qP1' f1 f2 f3 a a1 b b1 * qP1' f1 f2 f3 a a1 b b1 * b ∧
    E.G2 (fun y => φ (ψ y)) (fun y => φ (ψ y)) x =
      (qΘ' f1 f2 b b1 * a + qΘ'' f1 f2 f3 b b1 b2 * b - 2 * (qP1' f1 f2 f3 a a1 b b1 * f1 * b)) / 2 := by
  have hψ := hJ.smooth
  have hα := hJ.α_smooth
  have hβ := hJ.β_smooth
  have hf1 : S1 (deriv φ) := hφ.dsm
  have hf2 : S1 (deriv (deriv φ)) := hf1.dsm
  have hf3 : S1 (deriv (deriv (deriv φ))) := hf2.dsm
  have hα1 : S1 (deriv α) := hα.dsm
  have hβ1 : S1 (deriv β) := hβ.dsm
  set P1 : ℝ → ℝ := fun t => deriv φ t * α t + deriv (deriv φ) t * β t with hP1def
  have hP1s : S1 P1 := (hf1.mul hα).add (hf2.mul hβ)
  have hP1d : ∀ t, HasDerivAt P1 (qP1' (deriv φ t) (deriv (deriv φ) t) (deriv (deriv (deriv φ)) t)
      (α t) (deriv α t) (β t) (deriv β t)) t := fun t =>
    ((hf1.hasDerivAt t).mul (hα.hasDerivAt t)).add ((hf2.hasDerivAt t).mul (hβ.hasDerivAt t))
  have hP1deriv : deriv P1 = fun t => qP1' (deriv φ t) (deriv (deriv φ) t) (deriv (deriv (deriv φ)) t)
      (α t) (deriv α t) (β t) (deriv β t) := funext fun t => (hP1d t).deriv
  have hP1dd : ∀ t, HasDerivAt (deriv P1) (qP1'' (deriv φ t) (deriv (deriv φ) t) (deriv (deriv (deriv φ)) t)
      (deriv (deriv (deriv (deriv φ))) t) (α t) (deriv α t) (deriv (deriv α) t) (β t) (deriv β t)
      (deriv (deriv β) t)) t := by
    intro t
    rw [hP1deriv]
    exact (((hf2.hasDerivAt t).mul (hα.hasDerivAt t)).add ((hf1.hasDerivAt t).mul (hα1.hasDerivAt t))).add
      (((hf3.hasDerivAt t).mul (hβ.hasDerivAt t)).add ((hf2.hasDerivAt t).mul (hβ1.hasDerivAt t)))
  set Θ : ℝ → ℝ := fun t => deriv φ t * deriv φ t * β t with hΘdef
  have hΘs : S1 Θ := (hf1.mul hf1).mul hβ
  have hΘd : ∀ t, HasDerivAt Θ (qΘ' (deriv φ t) (deriv (deriv φ) t) (β t) (deriv β t)) t := fun t =>
    ((hf1.hasDerivAt t).mul (hf1.hasDerivAt t)).mul (hβ.hasDerivAt t)
  have hΘderiv : deriv Θ = fun t => qΘ' (deriv φ t) (deriv (deriv φ) t) (β t) (deriv β t) :=
    funext fun t => (hΘd t).deriv
  have hΘdd : ∀ t, HasDerivAt (deriv Θ) (qΘ'' (deriv φ t) (deriv (deriv φ) t) (deriv (deriv (deriv φ)) t)
      (β t) (deriv β t) (deriv (deriv β) t)) t := by
    intro t
    rw [hΘderiv]
    have hA := (((hf2.hasDerivAt t).mul (hf1.hasDerivAt t)).add ((hf1.hasDerivAt t).mul (hf2.hasDerivAt t))).mul
      (hβ.hasDerivAt t)
    have hB := ((hf1.hasDerivAt t).mul (hf1.hasDerivAt t)).mul (hβ1.hasDerivAt t)
    exact hA.add hB
  have hA : ∀ y, E.Γ (fun z => φ (ψ z)) (fun z => φ (ψ z)) y = Θ (ψ y) := fun y => by
    rw [E.Γ_comp1 hφ hφ hψ y, hJ.Γ_eq y]
  have hB : ∀ y, E.L (fun z => φ (ψ z)) y = P1 (ψ y) := fun y => by
    rw [E.L_comp1 hφ hψ y, hJ.L_eq y, hJ.Γ_eq y]
  have hbfun : E.L (fun z => φ (ψ z)) = fun y => P1 (ψ y) := funext hB
  have hafun : E.Γ (fun z => φ (ψ z)) (fun z => φ (ψ z)) = fun y => Θ (ψ y) := funext hA
  subst hs
  subst h1 h2 h3 h4 ha ha1 ha2 hb hb1 hb2
  refine ⟨hA x, hB x, ?_, ?_, ?_⟩
  · rw [hbfun, E.L_comp1 hP1s hψ x, hJ.L_eq x, hJ.Γ_eq x, (hP1d (ψ x)).deriv, (hP1dd (ψ x)).deriv]
  · rw [hbfun, E.Γ_comp1 hP1s hP1s hψ x, hJ.Γ_eq x, (hP1d (ψ x)).deriv]
  · unfold G2
    rw [hafun, hbfun, E.L_comp1 hΘs hψ x, E.Γ_comp1 hP1s hφ hψ x, E.Γ_comp1 hφ hP1s hψ x,
      hJ.L_eq x, hJ.Γ_eq x, (hΘd (ψ x)).deriv, (hΘdd (ψ x)).deriv, (hP1d (ψ x)).deriv]
    ring

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
