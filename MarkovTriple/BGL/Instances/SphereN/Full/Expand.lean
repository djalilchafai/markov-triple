import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Full.Series

/-!
# `L²(σ)` expansion into spherical harmonics (Round 32, stream Y, step 3a)

`V k` is the finite-dimensional space of restrictions of harmonic homogeneous polynomials of degree `k` inside `L²(σ)`.
By `harm_orth` and `dense_span_harm` the family `(V k)` is a Hilbert sum (Mathlib `IsHilbertSum.mkInternal`), so every
`u ∈ L²(σ)` is `Σ_k a_k` with `a_k ∈ V k` and `‖a_k‖ ≤ ‖u‖`.
-/

open MeasureTheory MvPolynomial
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.SphereN

variable {n : ℕ}

/-- harmonic homogeneous polynomials of degree `k` form a submodule. -/
def Hk (n k : ℕ) : Submodule ℝ (Pn n) where
  carrier := {p | IsHarm k p}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, by rw [lap_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨isHomogeneous_zero _ _ _, lap_zero⟩
  smul_mem' := fun c p hp => ⟨(MvPolynomial.mem_homogeneousSubmodule k _).1 (Submodule.smul_mem _ c ((MvPolynomial.mem_homogeneousSubmodule k _).2 hp.1)), by rw [lap_smul, hp.2, smul_zero]⟩

lemma mem_Hk {k : ℕ} {p : Pn n} : p ∈ Hk n k ↔ IsHarm k p := Iff.rfl

instance finiteDimensional_Hk (k : ℕ) : FiniteDimensional ℝ (Hk n k) := by
  have h1 : FiniteDimensional ℝ (homogeneousSubmodule (Fin n) ℝ k) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg (σ := Fin n) (R := ℝ) k)
  exact Submodule.finiteDimensional_of_le (S₂ := homogeneousSubmodule (Fin n) ℝ k)
    (fun p hp => (MvPolynomial.mem_homogeneousSubmodule k p).2 (mem_Hk.1 hp).1)

/-- polynomial `↦` class of its restriction. -/
noncomputable def Φ0 : Pn n →ₗ[ℝ] Lp ℝ 2 (σ n) :=
  (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ).toLinearMap.comp restrA.toLinearMap

lemma Φ0_apply (p : Pn n) : Φ0 p = ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ (restrA p) := rfl

lemma Φ0_eq_cls (hn : 2 ≤ n) (p : Pn n) :
    Φ0 p = (sphereDiffusion n hn).cls ⟨restr p, restr_mem p⟩ := (cls_restr hn p).symm

/-- the `k`-th harmonic space in `L²(σ)`. -/
noncomputable def Vk (n k : ℕ) : Submodule ℝ (Lp ℝ 2 (σ n)) := (Hk n k).map Φ0

instance finiteDimensional_Vk (k : ℕ) : FiniteDimensional ℝ (Vk n k) := by
  unfold Vk
  infer_instance

lemma inner_Φ0 (hn : 1 ≤ n) (p q : Pn n) :
    inner ℝ (Φ0 p) (Φ0 q) = ∫ x, restr p x * restr q x ∂σ n := by
  have := σ_isProbabilityMeasure hn
  rw [Φ0_apply, Φ0_apply, ContinuousMap.inner_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [restrA_apply, conj_trivial]
  ring

lemma norm_Φ0_sq (hn : 1 ≤ n) (p : Pn n) : ‖Φ0 p‖ ^ 2 = Nn n p := by
  rw [← real_inner_self_eq_norm_sq, inner_Φ0 hn]
  simp [Nn, pow_two]

lemma Vk_orth (hn : 2 ≤ n) {k k' : ℕ} (hk : k ≠ k') {v w : Lp ℝ 2 (σ n)} (hv : v ∈ Vk n k)
    (hw : w ∈ Vk n k') : inner ℝ v w = 0 := by
  obtain ⟨p, hp, rfl⟩ := hv
  obtain ⟨q, hq, rfl⟩ := hw
  rw [inner_Φ0 (Nat.one_le_of_lt hn)]
  exact harm_orth hn hp hq hk

lemma Vk_total (hn : 2 ≤ n) : ⊤ ≤ (⨆ k, Vk n k).topologicalClosure := by
  rw [← dense_span_harm hn]
  refine Submodule.topologicalClosure_mono ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨k, h, hh, hf⟩, rfl⟩
  refine Submodule.mem_iSup_of_mem k ⟨h, hh, ?_⟩
  rw [Φ0_eq_cls hn]
  congr 1
  exact Subtype.ext hf.symm

/-- **Hilbert sum decomposition**: every `u ∈ L²(σ)` is a sum of components `a_k ∈ V_k` of norm `≤ ‖u‖`. -/
theorem exists_expansion (hn : 2 ≤ n) (u : Lp ℝ 2 (σ n)) :
    ∃ a : ℕ → Lp ℝ 2 (σ n), (∀ k, a k ∈ Vk n k) ∧ (∀ k, ‖a k‖ ≤ ‖u‖) ∧ HasSum a u := by
  have hV : IsHilbertSum ℝ (fun k => Vk n k) fun k => (Vk n k).subtypeₗᵢ :=
    IsHilbertSum.mkInternal (fun k => Vk n k)
      (fun k k' hk => fun {v w} => by
        exact Vk_orth hn hk v.2 w.2)
      (Vk_total hn)
  set w := hV.linearIsometryEquiv u with hw
  refine ⟨fun k => (w k : Lp ℝ 2 (σ n)), fun k => (w k).2, fun k => ?_, ?_⟩
  · have h1 : ‖w k‖ ≤ ‖w‖ := lp.norm_apply_le_norm (by norm_num) w k
    have h2 : ‖w‖ = ‖u‖ := LinearIsometryEquiv.norm_map _ _
    calc ‖(w k : Lp ℝ 2 (σ n))‖ = ‖w k‖ := rfl
      _ ≤ ‖u‖ := h1.trans h2.le
  · have := hV.hasSum_linearIsometryEquiv_symm w
    rw [hw, LinearIsometryEquiv.symm_apply_apply] at this
    exact this

end MarkovTriple.BGL.SphereN
