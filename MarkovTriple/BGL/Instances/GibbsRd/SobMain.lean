import MarkovTriple.BGL.Instances.GibbsRd.SobCm

/-!
# Sobolev embedding for weak derivatives: main theorems (R16 Sob)

Interior (local) embedding `W^{m+d,1}_loc ⊂ C^m` (mixed-derivative route; NOT the sharp index `m + ⌊d/2⌋ + 1`),
for `L¹_loc` and (a fortiori) `L²_loc` weak derivatives; and the all-orders interface
`smooth_of_weak_all_orders`.  Smoothness `C^∞` is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (NOT `ω`).
-/

open MeasureTheory Filter Topology
open scoped ContDiff

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

/-- smooth cutoff, `= 1` on `closedBall 0 R`. -/
noncomputable def cutoff (R : ℕ) : (Fin d → ℝ) → ℝ :=
  (⟨(R : ℝ) + 1, (R : ℝ) + 2, by positivity, by linarith⟩ : ContDiffBump (0 : Fin d → ℝ))

theorem contDiff_cutoff (R : ℕ) : ContDiff ℝ ∞ (cutoff (d := d) R) := ContDiffBump.contDiff _

theorem hasCompactSupport_cutoff (R : ℕ) : HasCompactSupport (cutoff (d := d) R) :=
  ContDiffBump.hasCompactSupport _

theorem cutoff_eq_one {R : ℕ} {x : Fin d → ℝ} (hx : ‖x‖ < R) : cutoff R x = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (by simpa using (by linarith : ‖x‖ ≤ (R : ℝ) + 1))

theorem local_rep (m : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : HasSobL1 (m + d) f) (R : ℕ) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ ∀ᵐ x, ‖x‖ < R → f x = g x := by
  have hF : HasSobL1 (m + d) (fun x => cutoff R x * f x) :=
    HasSobL1.mul_smooth _ hf (contDiff_cutoff R)
  obtain ⟨g, hg, hFg, -⟩ := sob_core_contDiff (hasCompactSupport_cutoff (d := d) R) m
    (F := fun x => cutoff R x * f x)
    (Eventually.of_forall fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]) hF
  refine ⟨g, hg, ?_⟩
  filter_upwards [hFg] with x hx hxR
  rw [← hx, cutoff_eq_one hxR, one_mul]

/-- gluing of local representatives. -/
theorem exists_rep_of_local {m : WithTop ℕ∞} {f : (Fin d → ℝ) → ℝ}
    (h : ∀ R : ℕ, ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ m g ∧ ∀ᵐ x, ‖x‖ < R → f x = g x) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ m g ∧ f =ᵐ[volume] g := by
  choose g hg hae using h
  have agree : ∀ R S : ℕ, ∀ x : Fin d → ℝ, ‖x‖ < R → ‖x‖ < S → g R x = g S x := by
    intro R S x hR hS
    have hU : IsOpen (Metric.ball (0 : Fin d → ℝ) (min (R : ℝ) S)) := Metric.isOpen_ball
    have h1 : g R =ᵐ[volume.restrict (Metric.ball (0 : Fin d → ℝ) (min (R : ℝ) S))] g S := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
      filter_upwards [hae R, hae S] with y hy1 hy2 hyb
      have hyb' : ‖y‖ < min (R : ℝ) S := by simpa using hyb
      rw [← hy1 (lt_of_lt_of_le hyb' (min_le_left _ _)), ← hy2 (lt_of_lt_of_le hyb' (min_le_right _ _))]
    have := Measure.eqOn_open_of_ae_eq h1 hU (hg R).continuous.continuousOn (hg S).continuous.continuousOn
    exact this (by simpa using lt_min hR hS)
  let N : (Fin d → ℝ) → ℕ := fun x => ⌈‖x‖⌉₊ + 1
  have hN : ∀ x : Fin d → ℝ, ‖x‖ < N x := fun x => by
    have := Nat.le_ceil ‖x‖
    simp only [N]; push_cast; linarith
  refine ⟨fun x => g (N x) x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x0
    have hev : (fun x => g (N x) x) =ᶠ[𝓝 x0] g (N x0) := by
      have : Metric.ball (0 : Fin d → ℝ) (N x0) ∈ 𝓝 x0 :=
        Metric.isOpen_ball.mem_nhds (by simpa using hN x0)
      filter_upwards [this] with y hy
      exact agree _ _ y (hN y) (by simpa using hy)
    exact ((hg (N x0)).contDiffAt).congr_of_eventuallyEq hev
  · have : ∀ᵐ x, ∀ R : ℕ, ‖x‖ < R → f x = g R x := ae_all_iff.2 hae
    filter_upwards [this] with x hx
    exact hx (N x) (hN x)

/-- **Sobolev/Morrey embedding (interior, order `m + d`)**: `HasSobL1 (m+d) f` gives a `C^m` representative. -/
theorem sob_contDiff_rep (m : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : HasSobL1 (m + d) f) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ f =ᵐ[volume] g :=
  exists_rep_of_local fun R => local_rep m hf R

/-- Continuous representative: `W^{d,1}_loc ⊂ C`. -/
theorem sob_continuous_rep {f : (Fin d → ℝ) → ℝ} (hf : HasSobL1 d f) :
    ∃ g : (Fin d → ℝ) → ℝ, Continuous g ∧ f =ᵐ[volume] g := by
  obtain ⟨g, hg, h⟩ := sob_contDiff_rep 0 (by simpa using hf)
  exact ⟨g, (contDiff_zero (𝕜 := ℝ)).1 (by simpa using hg), h⟩

theorem sob_contDiff_rep_L2 (m : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : HasSobL2 (m + d) f) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ f =ᵐ[volume] g :=
  sob_contDiff_rep m (HasSobL2.toL1 _ hf)

theorem sob_continuous_rep_L2 {f : (Fin d → ℝ) → ℝ} (hf : HasSobL2 d f) :
    ∃ g : (Fin d → ℝ) → ℝ, Continuous g ∧ f =ᵐ[volume] g :=
  sob_continuous_rep (HasSobL2.toL1 _ hf)

/-- **Core interface**: all iterated weak derivatives in `L¹_loc` ⇒ `C^∞` representative. -/
theorem smooth_of_weak_all_orders_L1 {f : (Fin d → ℝ) → ℝ} (hf : ∀ k, HasSobL1 k f) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ f =ᵐ[volume] g := by
  choose g hg hfg using fun m : ℕ => sob_contDiff_rep m (hf (m + d))
  refine ⟨g 0, ?_, hfg 0⟩
  have : ∀ m : ℕ, g 0 = g m := fun m =>
    (Continuous.ae_eq_iff_eq volume (hg 0).continuous (hg m).continuous).1
      ((hfg 0).symm.trans (hfg m))
  have h2 : ContDiff ℝ ∞ (g 0) := by
    rw [contDiff_infty]
    intro m
    rw [this m]
    exact hg m
  exact h2

/-- **Core interface for the glue**: `f ∈ L²_loc` with all iterated weak derivatives (of every order) in
`L²_loc` has a `C^∞` representative (`ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)`, i.e. smooth, not analytic). -/
theorem smooth_of_weak_all_orders {f : (Fin d → ℝ) → ℝ} (hf : ∀ k, HasSobL2 k f) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ f =ᵐ[volume] g :=
  smooth_of_weak_all_orders_L1 fun k => HasSobL2.toL1 k (hf k)

end MarkovTriple.BGL.Instances.GibbsRd.Sob
