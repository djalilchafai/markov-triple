import Mathlib
import MarkovTriple.BGL.Theory.Extension.HessExt
import MarkovTriple.BGL.Theory.Extension.ClosedGamma

/-!
# Linear combinations of approximating sequences (round 15 gap closure; BGL p. 160)

`jL`, `jE` are linear; hence graph (form) convergent sequences can be combined linearly, and the limit of a
combination is the combination of the limits.  This is the only input needed to transfer linearity of the
`𝒜₀`-level classes `HH`, `GG2`, `GG` to the extensions `hessE`, `gamma2E`, `gammaE`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma jL_smul (c : ℝ) (a : T.A₀) : jL T (c • a) = c • jL T a := by
  show (DiffusionTriple.clsₗ T.toDiffusionTriple (c • a), DiffusionTriple.Lclsₗ T.toDiffusionTriple (c • a)) =
    c • (DiffusionTriple.clsₗ T.toDiffusionTriple a, DiffusionTriple.Lclsₗ T.toDiffusionTriple a)
  rw [map_smul, map_smul]; rfl

lemma jL_lin (a a' : T.A₀) (c : ℝ) : jL T (a + c • a') = jL T a + c • jL T a' := by
  rw [map_add, jL_smul]

lemma jE_smul (c : ℝ) (a : T.A₀) : jE T (c • a) = c • jE T a := by
  have : domElt T (c • a) = c • domElt T a := by
    apply Subtype.ext
    show DiffusionTriple.clsₗ T.toDiffusionTriple (c • a) = c • DiffusionTriple.clsₗ T.toDiffusionTriple a
    rw [map_smul]
  show ((domElt T (c • a) : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T) =
    c • ((domElt T a : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T)
  rw [this]
  exact UniformSpace.Completion.coe_smul c _

lemma jE_lin (a a' : T.A₀) (c : ℝ) : jE T (a + c • a') = jE T a + c • jE T a' := by
  rw [map_add, jE_smul]

/-- graph-convergent sequences combine linearly. -/
lemma GraphConv.lin {a a' : ℕ → T.A₀} {u u' w : Lp ℝ 2 T.μ}
    {hu : u ∈ T.toDiffusionTriple.generator.domain} {hu' : u' ∈ T.toDiffusionTriple.generator.domain}
    {hw : w ∈ T.toDiffusionTriple.generator.domain} (c : ℝ) (hwe : w = u + c • u')
    (ha : GraphConv T a u hu) (ha' : GraphConv T a' u' hu') :
    GraphConv T (fun k => a k + c • a' k) w hw := by
  unfold GraphConv at *
  have hsub : (⟨w, hw⟩ : T.toDiffusionTriple.generator.domain) = ⟨u, hu⟩ + c • ⟨u', hu'⟩ :=
    Subtype.ext hwe
  have hgen : T.toDiffusionTriple.generator ⟨w, hw⟩ =
      T.toDiffusionTriple.generator ⟨u, hu⟩ + c • T.toDiffusionTriple.generator ⟨u', hu'⟩ := by
    rw [hsub, LinearPMap.map_add, LinearPMap.map_smul]
  have : (w, T.toDiffusionTriple.generator ⟨w, hw⟩) =
      (u, T.toDiffusionTriple.generator ⟨u, hu⟩) + c • (u', T.toDiffusionTriple.generator ⟨u', hu'⟩) := by
    rw [hgen, hwe]; rfl
  rw [this]
  exact (ha.add (ha'.const_smul c)).congr (fun k => (jL_lin (a k) (a' k) c).symm)

/-- form-convergent sequences combine linearly. -/
lemma FormConv.lin {b b' : ℕ → T.A₀} {g g' w : T.formDomain} (c : ℝ) (hwe : w = g + c • g')
    (hb : FormConv T b g) (hb' : FormConv T b' g') :
    FormConv T (fun k => b k + c • b' k) w := by
  unfold FormConv at *
  have : (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm w =
      (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm g +
        c • (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm g' := by
    rw [hwe]; erw [map_add, map_smul]
  rw [this]
  exact (hb.add (hb'.const_smul c)).congr (fun k => (jE_lin (b k) (b' k) c).symm)

end FullTriple

end MarkovTriple.BGL
