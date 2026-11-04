import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Full

/-!
# Round 22 (E4), part N: the Brownian full triple on `(ℝ, Lebesgue)` is a genuinely non-compact finite-`n` `CD` instance

`lebesgueFull : FullTriple ℝ` (`𝒜₀ = C_c^∞(ℝ)`, `𝒜 = C^∞(ℝ)`, `μ` = Lebesgue, infinite) satisfies `CD(ρ,n)` for all `ρ ≤ 0`, `1 ≤ n ≤ ∞`
(`lebesgue_CD`).  Here: the exact characterisation `lebesgue_CD_iff` (`CD ρ n ↔ ρ ≤ 0 ∧ 1 ≤ n`), non-compactness, infinite mass and `𝒜 ≠ 𝒜₀`.
See `STATEMENTS_R22_E4.md`.  Dimension `d ≥ 2` is NOT covered.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

/-- **N1**: sharp curvature range for the Brownian full triple on `ℝ`: `CD(ρ,n) ↔ ρ ≤ 0 ∧ 1 ≤ n`. -/
theorem lebesgue_CD_iff {ρ : ℝ} {n : ℝ≥0∞} : lebesgueFull.CD ρ n ↔ ρ ≤ 0 ∧ 1 ≤ n := by
  refine ⟨fun h => ⟨?_, h.1⟩, fun h => lebesgue_CD h.1 h.2⟩
  have hf : (fun x : ℝ => x) ∈ lebesgueFull.A := mem_A.2 contDiff_id
  have h2 := h.2 _ hf
  have hμ : lebesgueFull.μ = volume := rfl
  have hsm : Sm (fun x : ℝ => x) := contDiff_id
  have hL : lebesgueFull.L (fun x : ℝ => x) = Lf (fun x : ℝ => x) := rfl
  have hLf : Lf (fun x : ℝ => x) = fun _ => 0 := by
    funext y; simp [Lf]
  have hΓ : lebesgueFull.toDiffusionTriple.ΓA (fun x : ℝ => x) (fun x : ℝ => x) =
      Gf (fun x : ℝ => x) (fun x : ℝ => x) := ΓA_eq_Gf hsm hsm
  have hG2 : ∀ x, lebesgueFull.toDiffusionTriple.Γ₂ (fun x : ℝ => x) (fun x : ℝ => x) x = 0 := by
    intro x
    have := Γ₂_eq hsm x
    rw [hLf] at this
    show lebesgueDiffusion.Γ₂ (fun x : ℝ => x) (fun x : ℝ => x) x = 0
    simpa using this
  rw [hμ] at h2
  have h3 : ∀ᵐ x ∂(volume : Measure ℝ), ρ ≤ 0 := by
    filter_upwards [h2] with x hx
    rw [hG2 x, hL, hLf, hΓ] at hx
    simpa [Gf] using hx
  by_contra hcon
  have h4 : ∀ᵐ x ∂(volume : Measure ℝ), False := h3.mono fun x hx => hcon hx
  have h5 := ae_iff.1 h4
  simp at h5

/-- **N2**: the instance lives on the non-compact space `ℝ` with infinite measure. -/
theorem lebesgueFull_noncompact : NoncompactSpace ℝ ∧ lebesgueFull.μ Set.univ = ⊤ :=
  ⟨inferInstance, by
    show (volume : Measure ℝ) Set.univ = ⊤
    rw [Real.volume_univ]⟩

/-- **N2**: `𝒜₀ ≠ 𝒜` as sets of functions (`1 ∈ 𝒜 \ 𝒜₀`: the constant `1` has no compact support). -/
theorem lebesgueFull_A_ne_A₀ : (lebesgueFull.A₀ : Set (ℝ → ℝ)) ≠ (lebesgueFull.A : Set (ℝ → ℝ)) := by
  intro h
  have h1 : (fun _ : ℝ => (1 : ℝ)) ∈ (lebesgueFull.A : Set (ℝ → ℝ)) :=
    lebesgueFull.A.one_mem
  rw [← h] at h1
  have hcs : HasCompactSupport (fun _ : ℝ => (1 : ℝ)) := cs h1
  have := hcs.isCompact
  have hts : tsupport (fun _ : ℝ => (1 : ℝ)) = Set.univ := by
    simp [tsupport, Function.support_const (one_ne_zero : (1 : ℝ) ≠ 0)]
  rw [hts] at this
  exact noncompact_univ ℝ this

end MarkovTriple.BGL.Lebesgue
