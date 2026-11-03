import MarkovTriple.BGL.Instances.GibbsRd.SobSharpCore

/-!
# Sharp Sobolev embedding `H^k_loc ⊂ C^m` for `k > m + d/2` (R17 SobSharp): main theorems

Statements: `STATEMENTS_R17_SobSharp.md`.  Textbook: Folland, *Real Analysis*, Thm 9.17; Evans §5.6.3 Thm 6;
Gilbarg–Trudinger Thm 7.26.  The index `k = m + ⌊d/2⌋ + 1` replaces `m + d` of `sob_contDiff_rep_L2`.
Smoothness `C^∞` is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (NOT `⊤ = ω`, analytic).
-/

open MeasureTheory Filter Topology
open scoped ContDiff

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem local_rep_sharp (m k : ℕ) (hk : d + 2 * m < 2 * k) {f : (Fin d → ℝ) → ℝ} (hf : HasSobL2 k f)
    (R : ℕ) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ ∀ᵐ x, ‖x‖ < R → f x = g x := by
  have hF : HasSobL2 k (fun x => cutoff R x * f x) :=
    HasSobL2.mul_smooth _ hf (contDiff_cutoff R)
  obtain ⟨g, hg, hFg⟩ := sob_core_sharp (hasCompactSupport_cutoff (d := d) R) (F := fun x => cutoff R x * f x)
    (Eventually.of_forall fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]) m k hk hF
  refine ⟨g, hg, ?_⟩
  filter_upwards [hFg] with x hx hxR
  rw [← hx, cutoff_eq_one hxR, one_mul]

/-- **Sharp Sobolev/Morrey embedding (interior)**: `f ∈ H^k_loc` (iterated weak derivatives up to order `k` in `L²_loc`)
with `k > m + d/2` (stated `d + 2 m < 2 k`) has a `C^m` representative. -/
theorem sob_contDiff_rep_sharp (m k : ℕ) (hk : d + 2 * m < 2 * k) {f : (Fin d → ℝ) → ℝ}
    (hf : HasSobL2 k f) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ f =ᵐ[volume] g :=
  exists_rep_of_local fun R => local_rep_sharp m k hk hf R

/-- Same, in the minimal-order form `k = m + ⌊d/2⌋ + 1`. -/
theorem sob_contDiff_rep_sharp' (m : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : HasSobL2 (m + d / 2 + 1) f) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ f =ᵐ[volume] g :=
  sob_contDiff_rep_sharp m _ (by omega) hf

/-- Continuous representative: `H^{⌊d/2⌋+1}_loc ⊂ C`. -/
theorem sob_continuous_rep_sharp {f : (Fin d → ℝ) → ℝ} (hf : HasSobL2 (d / 2 + 1) f) :
    ∃ g : (Fin d → ℝ) → ℝ, Continuous g ∧ f =ᵐ[volume] g := by
  obtain ⟨g, hg, h⟩ := sob_contDiff_rep_sharp' 0 (f := f) (by simpa using hf)
  exact ⟨g, (contDiff_zero (𝕜 := ℝ)).1 (by simpa using hg), h⟩

/-- All orders: `C^∞` representative, via the sharp embedding. -/
theorem smooth_of_weak_all_orders_sharp {f : (Fin d → ℝ) → ℝ} (hf : ∀ k, HasSobL2 k f) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ f =ᵐ[volume] g := by
  choose g hg hfg using fun m : ℕ => sob_contDiff_rep_sharp' m (hf (m + d / 2 + 1))
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

end MarkovTriple.BGL.Instances.GibbsRd.Sob
