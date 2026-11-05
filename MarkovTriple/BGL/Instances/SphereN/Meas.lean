import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Diff

/-!
# The surface measure `σ`, continuity/boundedness/density of `𝒜₀` (Round 28, stream L)
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

/-- the (un-normalised) surface measure of Mathlib (cone/radial construction). -/
noncomputable def σ0 (n : ℕ) : Measure (Sph n) := (volume : Measure (Ee n)).toSphere

/-- normalized surface measure. -/
noncomputable def σ (n : ℕ) : Measure (Sph n) := (σ0 n Set.univ)⁻¹ • σ0 n

lemma σ0_univ_ne_top (n : ℕ) : σ0 n Set.univ ≠ ∞ := by
  unfold σ0
  rw [Measure.toSphere_apply_univ]
  exact ENNReal.mul_ne_top (by simp) (measure_ball_lt_top).ne

lemma σ0_univ_ne_zero (hn : 1 ≤ n) : σ0 n Set.univ ≠ 0 := by
  have : Nontrivial (Ee n) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  intro h
  have := Measure.toSphere_ne_zero (E := Ee n) (μ := volume)
  apply this
  exact Measure.measure_univ_eq_zero.1 h

instance σ0_finite (n : ℕ) : IsFiniteMeasure (σ0 n) := ⟨lt_top_iff_ne_top.2 (σ0_univ_ne_top n)⟩

theorem σ_isProbabilityMeasure (hn : 1 ≤ n) : IsProbabilityMeasure (σ n) := by
  refine ⟨?_⟩
  simp only [σ, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (σ0_univ_ne_zero hn) (σ0_univ_ne_top n)

instance σ_finite (n : ℕ) : IsFiniteMeasure (σ n) := by
  unfold σ; infer_instance

lemma continuous_cv : Continuous (fun x : Sph n => cv (x : Ee n)) := by
  unfold cv
  exact (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val

lemma continuous_of_mem {f : Sph n → ℝ} (hf : f ∈ A₀S n) : Continuous f := by
  have h : f = fun x : Sph n => ext f (cv (x : Ee n)) := by funext x; rw [ext_cv]
  rw [h]
  have hc : ContinuousOn (ext f) {y | y ≠ 0} := (show SmO (ext f) from hf).continuousOn
  exact hc.comp_continuous continuous_cv fun x => cv_ne_zero x

lemma bounded_of_mem {f : Sph n → ℝ} (hf : f ∈ A₀S n) : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Sph n))).exists_bound_of_continuousOn
    (continuous_of_mem hf).continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

lemma memLp_of_mem {f : Sph n → ℝ} (hf : f ∈ A₀S n) (p : ℝ≥0∞) : MemLp f p (σ n) := by
  obtain ⟨C, hC⟩ := bounded_of_mem hf
  exact MemLp.of_bound (continuous_of_mem hf).aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa using hC x)

/-- the subalgebra of `C(S^{n-1}, ℝ)` of smooth functions. -/
def AC (n : ℕ) : Subalgebra ℝ C(Sph n, ℝ) where
  carrier := {g | (g : Sph n → ℝ) ∈ A₀S n}
  add_mem' := fun {f _g} hf hg => add_mem (show (f : Sph n → ℝ) ∈ A₀S n from hf) hg
  mul_mem' := fun {f _g} hf hg => mul_mem (show (f : Sph n → ℝ) ∈ A₀S n from hf) hg
  algebraMap_mem' := fun r => (A₀S n).algebraMap_mem r

lemma AC_sep : (AC n).SeparatesPoints := by
  intro x y hxy
  have hxy' : cv (x : Ee n) ≠ cv (y : Ee n) := by
    intro h
    apply hxy
    apply Subtype.ext
    ext i
    exact congrFun h i
  obtain ⟨i, hi⟩ : ∃ i, cv (x : Ee n) i ≠ cv (y : Ee n) i := by
    by_contra hcon
    apply hxy'
    funext j
    by_contra hj
    exact hcon ⟨j, hj⟩
  refine ⟨_, ⟨⟨fun z : Sph n => cv (z : Ee n) i, ?_⟩, ?_, rfl⟩, ?_⟩
  · exact (continuous_apply i).comp continuous_cv
  · exact A₀S_of_contDiff (F := fun y : Fin n → ℝ => y i) (contDiff_apply ℝ ℝ i)
  · exact hi

lemma AC_top : (AC n).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints (AC n) AC_sep

lemma dense_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {u : Lp ℝ p (σ n) | ∃ f ∈ A₀S n, (u : Sph n → ℝ) =ᵐ[σ n] f} := by
  have h1 : DenseRange (ContinuousMap.toLp (E := ℝ) p (σ n) ℝ : C(Sph n, ℝ) →L[ℝ] Lp ℝ p (σ n)) :=
    ContinuousMap.toLp_denseRange ℝ (σ n) ℝ hp
  have h2 : Dense ((AC n) : Set C(Sph n, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, AC_top]; rfl
  have h3 := h1.dense_image (ContinuousMap.toLp (E := ℝ) p (σ n) ℝ).continuous h2
  refine h3.mono ?_
  rintro _ ⟨F, hF, rfl⟩
  exact ⟨F, hF, ContinuousMap.coeFn_toLp _ _⟩

end MarkovTriple.BGL.SphereN
