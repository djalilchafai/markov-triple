import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdZL
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdCalc
import MarkovTriple.BGL.Instances.GibbsRd.Cutoff

/-!
# `Core2` on `ℝ^d`: the cut-off commutator expansions and the three graph-norm estimates (R18, Stream A3)

For `v` smooth and the cut-offs `χ_n = cut (n+1)`, with `P = L χ_n`:
* `L(χ v) − L v = (χ − 1) L v + v P + 2 Γ(χ, v)`;
* `L(L(χ v)) − L L v = (χ − 1) L L v + 2 P L v + 4 Γ(χ, L v) + v L P + 4 Γ(P, v) + 4 Σ χ_ij v_ij + 4 Σ V_ij χ_i v_j`.
`CoeffGood V`: all the coefficient families occurring are `Good` (continuous, uniformly bounded, eventually zero).
Then `cutoff_ZL`: the three differences tend to `0` in `L²(μ)` as soon as `v, ∇v, ∇²v ∈ L²(μ)` and `L v, L L v ∈ L²(μ)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

section pointwise
variable {V v χ : Rd d → ℝ}

lemma Lr_Lr_mul (hV : Sm V) (hv : Sm v) (hχ : Sm χ) (x : Rd d) :
    Lr V (Lr V (χ * v)) x = χ x * Lr V (Lr V v) x + 2 * (Lr V v x * Lr V χ x) + 4 * Gr χ (Lr V v) x +
      v x * Lr V (Lr V χ) x + 4 * Gr (Lr V χ) v x +
      4 * ∑ i, ∑ j, pderiv (pderiv χ i) j x * pderiv (pderiv v i) j x +
      4 * ∑ i, ∑ j, pderiv (pderiv V i) j x * pderiv χ i x * pderiv v j x := by
  have hLv : Sm (Lr V v) := sm_Lr hV hv
  have hLχ : Sm (Lr V χ) := sm_Lr hV hχ
  have e1 : Lr V (χ * v) = fun y => χ y * Lr V v y + 1 * (v y * Lr V χ y + 2 * Gr χ v y) := by
    funext y
    rw [Lr_mul hχ hv y]; ring
  have hs1 : Sm (fun y => χ y * Lr V v y) := hχ.mul hLv
  have hs2 : Sm (fun y => v y * Lr V χ y + 2 * Gr χ v y) :=
    (hv.mul hLχ).add (contDiff_const.mul (sm_Gr' hχ hv))
  rw [e1, Lr_add_smul hs1 hs2 1 x]
  have h1 : Lr V (fun y => χ y * Lr V v y) x = χ x * Lr V (Lr V v) x + Lr V v x * Lr V χ x +
      2 * Gr χ (Lr V v) x := Lr_mul hχ hLv x
  have h2 := Lr_remainder hV hv hχ x
  rw [h1, h2]
  ring

lemma Lr_chi_v (hv : Sm v) (hχ : Sm χ) (x : Rd d) :
    Lr V (χ * v) x = χ x * Lr V v x + v x * Lr V χ x + 2 * Gr χ v x := Lr_mul hχ hv x

end pointwise

/-- the cut-off functions -/
noncomputable abbrev chi (n : ℕ) : Rd d → ℝ := cut ((n : ℝ) + 1)

/-- all coefficient families of the cut-off commutators are `Good`. -/
def CoeffGood (V : Rd d → ℝ) : Prop :=
  Good (fun (n : ℕ) (x : Rd d) => chi n x - 1) ∧ Good (fun (n : ℕ) (x : Rd d) => Lr V (chi n) x) ∧
  (∀ i, Good (fun (n : ℕ) (x : Rd d) => pderiv (chi n) i x)) ∧
  (∀ i j, Good (fun (n : ℕ) (x : Rd d) => pderiv (pderiv (chi n) i) j x)) ∧
  (∀ i, Good (fun (n : ℕ) (x : Rd d) => pderiv (Lr V (chi n)) i x)) ∧
  Good (fun (n : ℕ) (x : Rd d) => Lr V (Lr V (chi n)) x) ∧
  (∀ i j, Good (fun (n : ℕ) (x : Rd d) => pderiv (pderiv V i) j x * pderiv (chi n) i x))

/-- **the three graph-norm cut-off estimates**: `χ_n v → v`, `L(χ_n v) → L v`, `L²(χ_n v) → L² v` in `L²(μ)`. -/
theorem cutoff_ZL {μ : Measure (Rd d)} {V v : Rd d → ℝ} (hV : Sm V) (hg : CoeffGood V) (hv : Sm v)
    (h0 : MemLp v 2 μ) (h1 : ∀ i, MemLp (pderiv v i) 2 μ) (h2 : ∀ i j, MemLp (pderiv (pderiv v i) j) 2 μ)
    (hLv : MemLp (Lr V v) 2 μ) (hLLv : MemLp (Lr V (Lr V v)) 2 μ)
    (hLv1 : ∀ i, MemLp (pderiv (Lr V v) i) 2 μ) :
    ZL μ (fun n x => chi n x * v x - v x) ∧
    ZL μ (fun n x => Lr V (chi n * v) x - Lr V v x) ∧
    ZL μ (fun n x => Lr V (Lr V (chi n * v)) x - Lr V (Lr V v) x) := by
  obtain ⟨g1, gP, gC, gCC, gPi, gLP, gVC⟩ := hg
  have hχ : ∀ n, Sm (chi n : Rd d → ℝ) := fun n => sm_cut _
  refine ⟨?_, ?_, ?_⟩
  · exact (ZL.of_good g1 h0).congr (fun n x => by ring)
  · have hsum : ZL μ (fun n x => ∑ i, pderiv (chi n) i x * pderiv v i x) :=
      ZL.finset_sum _ (fun i _ => ZL.of_good (gC i) (h1 i))
    refine (((ZL.of_good g1 hLv).add (ZL.of_good gP h0)).add (hsum.const_mul 2)).congr (fun n x => ?_)
    rw [Lr_chi_v hv (hχ n) x]
    simp only [Gr]
    ring
  · have s1 : ZL μ (fun n x => (chi n x - 1) * Lr V (Lr V v) x) := ZL.of_good g1 hLLv
    have s2 : ZL μ (fun n x => Lr V (chi n) x * Lr V v x) := ZL.of_good gP hLv
    have s3 : ZL μ (fun n x => ∑ i, pderiv (chi n) i x * pderiv (Lr V v) i x) :=
      ZL.finset_sum _ (fun i _ => ZL.of_good (gC i) (hLv1 i))
    have s4 : ZL μ (fun n x => Lr V (Lr V (chi n)) x * v x) := ZL.of_good gLP h0
    have s5 : ZL μ (fun n x => ∑ i, pderiv (Lr V (chi n)) i x * pderiv v i x) :=
      ZL.finset_sum _ (fun i _ => ZL.of_good (gPi i) (h1 i))
    have s6 : ZL μ (fun n x => ∑ i, ∑ j, pderiv (pderiv (chi n) i) j x * pderiv (pderiv v i) j x) :=
      ZL.finset_sum _ (fun i _ => ZL.finset_sum _ (fun j _ => ZL.of_good (gCC i j) (h2 i j)))
    have s7 : ZL μ (fun n x => ∑ i, ∑ j,
        pderiv (pderiv V i) j x * pderiv (chi n) i x * pderiv v j x) :=
      ZL.finset_sum _ (fun i _ => ZL.finset_sum _ (fun j _ => ZL.of_good (gVC i j) (h1 j)))
    refine ((((((s1.add (s2.const_mul 2)).add (s3.const_mul 4)).add s4).add (s5.const_mul 4)).add
      (s6.const_mul 4)).add (s7.const_mul 4)).congr (fun n x => ?_)
    rw [Lr_Lr_mul hV hv (hχ n) x]
    simp only [Gr]
    ring

end MarkovTriple.BGL.Instances.GibbsRd
