import Mathlib
import MarkovTriple.BGL.Theory.Extension.Core2Reduce
import MarkovTriple.BGL.Instances.Riemannian.R24.Core2Criterion

/-!
# Round 26 (stream I): `Core2` -- orthogonality form and the eigenbasis criterion

* `FullTriple.core2_iff_orth` (I1): `Core2` iff no nonzero `L²`-vector is orthogonal to `(1-L)²𝒜₀`.
* `FullTriple.core2_of_eigen` (I2): if `𝒜₀` contains eigenfunctions of `L` (eigenvalue `-c`, `c ≥ 0`) whose classes span
  a dense subspace of `L²`, then `Core2` holds.

See `STATEMENTS_R26_I.md`.  No new axioms.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- **I1.**  `Core2` is exactly the absence of a nonzero `L²`-vector orthogonal to `(1-L)²𝒜₀`. -/
theorem core2_iff_orth :
    T.Core2 ↔ ∀ w : Lp ℝ 2 T.μ, (∀ b : T.A₀, inner ℝ (Ψₗ T b) w = 0) → w = 0 := by
  rw [core2_iff_dense]
  have h : Dense (Set.range (Ψₗ T)) ↔ (LinearMap.range (Ψₗ T)).topologicalClosure = ⊤ := by
    rw [← Submodule.dense_iff_topologicalClosure_eq_top]; rfl
  rw [h, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  refine forall_congr' fun w => ?_
  rw [Submodule.mem_orthogonal]
  have e : (∀ u ∈ LinearMap.range (Ψₗ T), inner ℝ u w = 0) ↔ ∀ b, inner ℝ (Ψₗ T b) w = 0 :=
    ⟨fun H b => H _ ⟨b, rfl⟩, fun H u ⟨b, hb⟩ => hb ▸ H b⟩
  rw [e]

/-- an eigenfunction `φ ∈ 𝒜₀` has `[L φ] = -c [φ]`. -/
lemma Lcls_of_eigen {φ : T.A₀} {c : ℝ} (hL : T.L φ.1 =ᵐ[T.μ] fun x => -c * φ.1 x) :
    T.toDiffusionTriple.Lcls φ = (-c) • T.toDiffusionTriple.cls φ := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple φ,
    DiffusionTriple.coeFn_cls T.toDiffusionTriple φ,
    Lp.coeFn_smul (-c) (T.toDiffusionTriple.cls φ), hL] with x e1 e2 e3 e4
  rw [e3, Pi.smul_apply, e2, e1, smul_eq_mul]
  exact e4

/-- an eigenfunction `φ ∈ 𝒜₀` has `[L L φ] = c² [φ]`. -/
lemma LL_of_eigen {φ : T.A₀} {c : ℝ} (hL : T.L φ.1 =ᵐ[T.μ] fun x => -c * φ.1 x) :
    LLₗ T φ = (c ^ 2) • T.toDiffusionTriple.cls φ := by
  refine Lp.ext ?_
  have hφ := T.A₀_le _ φ.2
  have hs : (fun x => -c * φ.1 x) = (-c) • φ.1 := by funext x; simp
  rw [hs] at hL
  have h1 : T.L (T.L φ.1) =ᵐ[T.μ] T.L ((-c) • φ.1) :=
    L_congr_A T (T.L_mem_A _ hφ) (T.A.smul_mem hφ _) hL
  have h2 : T.L ((-c) • φ.1) =ᵐ[T.μ] (-c) • T.L φ.1 :=
    DiffusionTriple.L_smul_ae T.toDiffusionTriple (-c) φ.2
  filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple
      (⟨T.L φ.1, T.L_mem φ.1 φ.2⟩ : T.A₀),
    DiffusionTriple.coeFn_cls T.toDiffusionTriple φ,
    Lp.coeFn_smul (c ^ 2) (T.toDiffusionTriple.cls φ), h1, h2, hL] with x e1 e2 e3 e4 e5 e6
  have e1' : ((LLₗ T φ : Lp ℝ 2 T.μ) : E → ℝ) x = T.L (T.L φ.1) x := e1
  rw [e1', e3, Pi.smul_apply, e2, e4, e5]
  simp only [Pi.smul_apply, smul_eq_mul] at e6 ⊢
  rw [e6]; ring

/-- **I2.**  `Core2` from a dense family of eigenfunctions in `𝒜₀`. -/
theorem core2_of_eigen (S : Set T.A₀) (c : T.A₀ → ℝ) (hc : ∀ φ ∈ S, 0 ≤ c φ)
    (hL : ∀ φ ∈ S, T.L φ.1 =ᵐ[T.μ] fun x => -c φ * φ.1 x)
    (hd : (Submodule.span ℝ (T.toDiffusionTriple.cls '' S)).topologicalClosure = ⊤) : T.Core2 := by
  apply core2_of_dense
  have hsub : Submodule.span ℝ (T.toDiffusionTriple.cls '' S) ≤ LinearMap.range (Ψₗ T) := by
    rw [Submodule.span_le]
    rintro _ ⟨φ, hφ, rfl⟩
    have hpos : (0 : ℝ) < (1 + c φ) ^ 2 := by have := hc φ hφ; positivity
    refine ⟨(((1 + c φ) ^ 2)⁻¹) • φ, ?_⟩
    rw [map_smul]
    have : Ψₗ T φ = ((1 + c φ) ^ 2) • T.toDiffusionTriple.cls φ := by
      show (T.toDiffusionTriple.cls φ - T.toDiffusionTriple.Lcls φ) -
        (T.toDiffusionTriple.Lcls φ - LLₗ T φ) = _
      rw [Lcls_of_eigen (hL φ hφ), LL_of_eigen (hL φ hφ)]
      module
    rw [this, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  have hdense : (LinearMap.range (Ψₗ T)).topologicalClosure = ⊤ :=
    top_le_iff.1 (hd ▸ Submodule.topologicalClosure_mono hsub)
  have := Submodule.dense_iff_topologicalClosure_eq_top.2 hdense
  exact this

/-- Variant of I2 with the eigenvalue existentially quantified (convenience; same content). -/
theorem core2_of_eigen' (S : Set T.A₀)
    (hL : ∀ φ ∈ S, ∃ c : ℝ, 0 ≤ c ∧ T.L φ.1 =ᵐ[T.μ] fun x => -c * φ.1 x)
    (hd : (Submodule.span ℝ (T.toDiffusionTriple.cls '' S)).topologicalClosure = ⊤) : T.Core2 := by
  classical
  refine core2_of_eigen S (fun φ => if h : φ ∈ S then Classical.choose (hL φ h) else 0) ?_ ?_ hd
  · intro φ hφ
    simp only [hφ, ↓reduceDIte]
    exact (Classical.choose_spec (hL φ hφ)).1
  · intro φ hφ
    simp only [hφ, ↓reduceDIte]
    exact (Classical.choose_spec (hL φ hφ)).2

end FullTriple

end MarkovTriple.BGL
