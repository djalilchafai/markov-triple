import MarkovTriple.BGL.Instances.GibbsRd.SobWeak

/-!
# `L²_loc` versions of the weak-derivative calculus (R17 SobSharp)

`HasSobL2` analogues of `HasSobL1.add`, `HasSobL1.mul_smooth`, `exists_weakIter`, and
`MemLp f 2 volume` for `L²_loc` functions vanishing a.e. off a compact set.
-/

open MeasureTheory Filter Topology
open scoped ContDiff

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem HasSobL2.locL2 : ∀ (k : ℕ) {f : (Fin d → ℝ) → ℝ}, HasSobL2 k f → LocL2 f
  | 0, _, h => h
  | _ + 1, _, h => h.1

theorem HasSobL2.mono : ∀ (k : ℕ) {f : (Fin d → ℝ) → ℝ}, HasSobL2 (k + 1) f → HasSobL2 k f
  | 0, _, h => h.1
  | k + 1, _, h => ⟨h.1, fun i => by
      obtain ⟨g, hg, hg2⟩ := h.2 i
      exact ⟨g, hg, HasSobL2.mono k hg2⟩⟩

theorem LocL2.add {a b : (Fin d → ℝ) → ℝ} (ha : LocL2 a) (hb : LocL2 b) : LocL2 (fun x => a x + b x) :=
  fun K hK => (ha K hK).add (hb K hK)

theorem LocL2.mul_cont {f χ : (Fin d → ℝ) → ℝ} (hf : LocL2 f) (hχ : Continuous χ) :
    LocL2 (fun x => χ x * f x) := by
  intro K hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hχ.continuousOn
  refine (hf K hK).of_le_mul (c := C) ((hχ.aestronglyMeasurable).mul (hf K hK).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)

theorem HasSobL2.add : ∀ (k : ℕ) {a b : (Fin d → ℝ) → ℝ}, HasSobL2 k a → HasSobL2 k b →
    HasSobL2 k (fun x => a x + b x)
  | 0, _, _, ha, hb => LocL2.add ha hb
  | k + 1, _, _, ha, hb => ⟨LocL2.add ha.1 hb.1, fun i => by
      obtain ⟨g₁, hg₁, hk₁⟩ := ha.2 i
      obtain ⟨g₂, hg₂, hk₂⟩ := hb.2 i
      exact ⟨_, hg₁.add hg₂, HasSobL2.add k hk₁ hk₂⟩⟩

theorem HasSobL2.mul_smooth : ∀ (k : ℕ) {f χ : (Fin d → ℝ) → ℝ}, HasSobL2 k f → ContDiff ℝ ∞ χ →
    HasSobL2 k (fun x => χ x * f x)
  | 0, _, _, hf, hχ => LocL2.mul_cont hf hχ.continuous
  | k + 1, f, χ, hf, hχ => ⟨LocL2.mul_cont hf.1 hχ.continuous, fun i => by
      obtain ⟨g, hg, hk⟩ := hf.2 i
      refine ⟨_, hg.mul_smooth hχ, HasSobL2.add k (HasSobL2.mul_smooth k hk hχ) ?_⟩
      exact HasSobL2.mul_smooth k (HasSobL2.mono k hf) (contDiff_pd i hχ)⟩

theorem exists_weakIter_L2 : ∀ (l : List (Fin d)) (k : ℕ) {f : (Fin d → ℝ) → ℝ}, l.length ≤ k →
    HasSobL2 k f → ∃ g, WeakIter l f g ∧ HasSobL2 (k - l.length) g
  | [], k, f, _, hf => ⟨f, rfl, by simpa using hf⟩
  | i :: l, k, f, hlk, hf => by
    have hlk' : l.length ≤ k := by simp at hlk; omega
    obtain ⟨h, hh, hh'⟩ := exists_weakIter_L2 l k hlk' hf
    have hpos : k - l.length = (k - (i :: l).length) + 1 := by simp at hlk ⊢; omega
    rw [hpos] at hh'
    obtain ⟨g, hg, hg'⟩ := hh'.2 i
    exact ⟨g, ⟨h, hh, hg⟩, hg'⟩

/-- an `L²_loc` function vanishing a.e. off a compact set is in `L²`. -/
theorem memLp_of_locL2 {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0) {f : (Fin d → ℝ) → ℝ}
    (hf : LocL2 f) (h0 : ∀ᵐ x, x ∉ K0 → f x = 0) : MemLp f 2 := by
  have h1 : MemLp (K0.indicator f) 2 := (memLp_indicator_iff_restrict hK0.measurableSet).2 (hf K0 hK0)
  refine h1.ae_eq ?_
  filter_upwards [h0] with x hx
  by_cases hxK : x ∈ K0
  · simp [hxK]
  · simp [hxK, hx hxK]

theorem integrable_of_locL2 {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0) {f : (Fin d → ℝ) → ℝ}
    (hf : LocL2 f) (h0 : ∀ᵐ x, x ∉ K0 → f x = 0) : Integrable f :=
  ((hf.locallyIntegrable).integrableOn_isCompact hK0).integrable_of_ae_notMem_eq_zero
    (by filter_upwards [h0] with x hx h using hx h)

end MarkovTriple.BGL.Instances.GibbsRd.Sob
