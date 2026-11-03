import Mathlib
import MarkovTriple.BGL.Instances.SphereOpen.Triple
import MarkovTriple.BGL.Instances.Sphere.Semi

/-!
# Transport of the Friedrichs semigroup and resolvent (R17 Noncompact, N4)

`restrC : L²(μZ) → L²(μO)` is a unitary map with `restrC [f] = [f ∘ val]` for `f ∈ 𝒜_Z`.  The classes of
the eigenfunctions `U_k` span a dense subspace and are eigenvectors of `L` of the open triple, so by
`DiffusionTriple.R_cls_eigen` / `semigroup_cls_eigen` both `R` and `P_t` of `oT` intertwine with those of
the sphere on that dense subspace, hence everywhere by continuity.
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.Instances.SphereOpen

open MarkovTriple.BGL.Instances.Sphere

/-- the unitary restriction `L²(μZ) → L²(μO)` as a continuous linear map. -/
noncomputable def restrC : Lp ℝ 2 μZ →L[ℝ] Lp ℝ 2 μO :=
  (restrL 2).mkContinuous 1 (fun u => by rw [one_mul, norm_restrL])

lemma restrC_apply (u : Lp ℝ 2 μZ) : restrC u = restrL 2 u := rfl

lemma norm_restrC (u : Lp ℝ 2 μZ) : ‖restrC u‖ = ‖u‖ := norm_restrL 2 u

lemma restrC_injective : Function.Injective restrC := by
  intro u v h
  have : ‖u - v‖ = 0 := by
    rw [← norm_restrC, map_sub, h, sub_self, norm_zero]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

lemma restrC_surjective : Function.Surjective restrC := restrL_surjective 2

/-- `[f] ↦ [f ∘ val]`. -/
lemma restrC_cls {f : Zon → ℝ} (hf : f ∈ AZ) :
    restrC (sT.cls ⟨f, hf⟩) = oT.cls ⟨f ∘ jO, comp_mem_AO hf⟩ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restrL 2 (sT.cls ⟨f, hf⟩),
    ae_comap_jO (DiffusionTriple.coeFn_cls sT ⟨f, hf⟩),
    DiffusionTriple.coeFn_cls oT ⟨f ∘ jO, comp_mem_AO hf⟩] with x h1 h2 h3
  rw [restrC_apply, h1, h3]
  exact h2

lemma oT_L_UZ (k : ℕ) (x : ZonO) : oT.L (UZ k ∘ jO) x = -lamZ k * (UZ k ∘ jO) x := by
  show LO (UZ k ∘ jO) x = _
  rw [LO_comp (UZ_mem k)]
  show LZ (UZ k) (jO x) = _
  rw [LZ_UZ]
  rfl

lemma restrC_eZ (k : ℕ) : restrC (eZ k) = oT.cls ⟨UZ k ∘ jO, comp_mem_AO (UZ_mem k)⟩ :=
  restrC_cls (UZ_mem k)

lemma dense_span_eZ' : Dense ((Submodule.span ℝ (Set.range eZ) : Submodule ℝ (Lp ℝ 2 μZ)) : Set (Lp ℝ 2 μZ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact eq_top_iff.2 dense_span_eZ

/-- the Friedrichs resolvent of the open triple. -/
noncomputable abbrev RO : Lp ℝ 2 μO →L[ℝ] Lp ℝ 2 μO := (DiffusionTriple.formData oT).R

/-- the Friedrichs semigroup of the open triple. -/
noncomputable abbrev PO (t : ℝ≥0) : Lp ℝ 2 μO →L[ℝ] Lp ℝ 2 μO := oT.semigroup t

lemma RO_restrC (u : Lp ℝ 2 μZ) : RO (restrC u) = restrC (RZ u) := by
  have h : RO.comp restrC = restrC.comp RZ := by
    refine ContinuousLinearMap.ext_on dense_span_eZ' ?_
    rintro _ ⟨k, rfl⟩
    show RO (restrC (eZ k)) = restrC (RZ (eZ k))
    rw [restrC_eZ, RZ_eZ, map_smul]
    exact DiffusionTriple.R_cls_eigen oT ⟨UZ k ∘ jO, comp_mem_AO (UZ_mem k)⟩ (lamZ_nonneg k)
      (DiffusionTriple.Lcls_eq_smul oT (oT_L_UZ k)) |>.trans (by rw [restrC_eZ])
  exact congrArg (fun F => F u) h

lemma PO_restrC (t : ℝ≥0) (u : Lp ℝ 2 μZ) : PO t (restrC u) = restrC (PZ t u) := by
  have h : (PO t).comp restrC = restrC.comp (PZ t) := by
    refine ContinuousLinearMap.ext_on dense_span_eZ' ?_
    rintro _ ⟨k, rfl⟩
    show PO t (restrC (eZ k)) = restrC (PZ t (eZ k))
    rw [restrC_eZ, semigroup_eZ, map_smul, restrC_eZ]
    exact DiffusionTriple.semigroup_cls_eigen oT ⟨UZ k ∘ jO, comp_mem_AO (UZ_mem k)⟩
      (lamZ_nonneg k) (oT_L_UZ k) t
  exact congrArg (fun F => F u) h

/-! ### F8 and invariance -/

theorem semigroup_cls_mem_O (t : ℝ≥0) (f : oT.A₀) :
    ∃ g ∈ AO, (oT.semigroup t (oT.cls f) : ZonO → ℝ) =ᵐ[μO] g := by
  obtain ⟨f0, hf0, hf⟩ := mem_A0O.1 f.2
  have hfe : f = ⟨f0 ∘ jO, comp_mem_AO hf0⟩ := Subtype.ext hf
  subst hfe
  obtain ⟨g, hg, hae⟩ := semigroup_cls_mem t ⟨f0, hf0⟩
  refine ⟨g ∘ jO, comp_mem_AO hg, ?_⟩
  have e : oT.cls ⟨f0 ∘ jO, comp_mem_AO hf0⟩ = restrC (sT.cls ⟨f0, hf0⟩) := (restrC_cls hf0).symm
  rw [e]
  show (PO t (restrC (sT.cls ⟨f0, hf0⟩)) : ZonO → ℝ) =ᵐ[μO] _
  rw [PO_restrC]
  filter_upwards [coeFn_restrL 2 (PZ t (sT.cls ⟨f0, hf0⟩)), ae_comap_jO hae] with x h1 h2
  rw [restrC_apply, h1]
  exact h2

theorem semigroup_invariant_O (t : ℝ≥0) (f : oT.A₀) :
    ∃ g : oT.A₀, oT.semigroup t (oT.cls f) = oT.cls g := by
  obtain ⟨g, hg, hae⟩ := semigroup_cls_mem_O t f
  exact ⟨⟨g, hg⟩, Lp.ext (hae.trans (DiffusionTriple.coeFn_cls oT ⟨g, hg⟩).symm)⟩

/-! ### ergodicity (S10) and conservativeness (S11) -/

/-- the fixed points of the sphere resolvent are constants (the proof of `sphere_ergodic`). -/
lemma const_of_RZ_fixed {u : Lp ℝ 2 μZ} (hR' : RZ u = u) : ∃ c : ℝ, (u : Zon → ℝ) =ᵐ[μZ] fun _ => c := by
  have hs := bZ.hasSum_repr u
  have hz : ∀ k, k ≠ 0 → bZ.repr u k = 0 := by
    intro k hk
    rw [bZ.repr_apply_apply, bZ_apply]
    exact inner_eq_zero_of_fixed hk hR'
  have h1 : HasSum (fun k : ℕ => bZ.repr u k • bZ k) (bZ.repr u 0 • bZ 0) :=
    hasSum_single 0 (fun k hk => by rw [hz k hk, zero_smul])
  have h2 := hs.unique h1
  refine ⟨bZ.repr u 0, ?_⟩
  filter_upwards [Lp.coeFn_smul (bZ.repr u 0) (bZ 0), coeFn_eZ_zero] with x hx hy
  have : (u : Zon → ℝ) x = (bZ.repr u 0 • bZ 0 : Lp ℝ 2 μZ) x := by
    rw [← h2]
  rw [this, hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [bZ_apply, hy, mul_one]

/-- **S10** for the open triple. -/
theorem open_ergodic (u : Lp ℝ 2 oT.μ) (hu : u ∈ oT.generator.domain)
    (hG : oT.generator ⟨u, hu⟩ = 0) : ∃ c : ℝ, (u : ZonO → ℝ) =ᵐ[oT.μ] fun _ => c := by
  have hR : RO (u - 0) = u := ((DiffusionTriple.formData oT).generator_apply_eq_iff hu 0).1 hG
  rw [sub_zero] at hR
  obtain ⟨v, hv⟩ := restrC_surjective u
  have h1 : restrC (RZ v) = restrC v := by rw [← RO_restrC, hv, hR]
  have h2 : RZ v = v := restrC_injective h1
  obtain ⟨c, hc⟩ := const_of_RZ_fixed h2
  refine ⟨c, ?_⟩
  filter_upwards [coeFn_restrL 2 v, ae_comap_jO hc] with x h3 h4
  rw [← hv, restrC_apply, h3]
  exact h4

lemma restrC_one2 : restrC sT.one2 = oT.one2 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restrL 2 sT.one2, ae_comap_jO (DiffusionTriple.coeFn_one2 (T := sT)),
    DiffusionTriple.coeFn_one2 (T := oT)] with x h1 h2 h3
  rw [restrC_apply, h1, h3]
  exact h2

/-- `P_t 1 = 1` for the open triple. -/
theorem semigroup_one_O (t : ℝ≥0) : oT.semigroup t oT.one2 = oT.one2 := by
  rw [← restrC_one2]
  show PO t (restrC sT.one2) = _
  rw [PO_restrC, semigroup_one]

end MarkovTriple.BGL.Instances.SphereOpen
