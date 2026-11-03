import Mathlib

/-!
# Sobolev embedding, definitions (R16 Sob)

`WeakDeriv f g i` : `g` is the weak `i`-th partial derivative of `f` on `ℝ^d` (test functions
`C_c^∞(ℝ^d)`).  NOTE on `⊤`: in current Mathlib `ContDiff ℝ ⊤` (with `⊤ : WithTop ℕ∞`) means
*analytic* (`ω`), and an analytic compactly supported function vanishes; we therefore use
`ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. `C^∞`), the intended meaning of the shared definition.
-/

open MeasureTheory
open scoped ContDiff

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

/-- Weak derivative (shared definition; `ContDiff ℝ ∞` = `C^∞`). -/
def WeakDeriv {d : ℕ} (f g : (Fin d → ℝ) → ℝ) (i : Fin d) : Prop :=
  LocallyIntegrable f ∧ LocallyIntegrable g ∧
    ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, f x * (fderiv ℝ φ x (Pi.single i 1)) = - ∫ x, g x * φ x

/-- `f ∈ L²_loc`. -/
def LocL2 {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ K : Set (Fin d → ℝ), IsCompact K → MemLp f 2 (volume.restrict K)

/-- Iterated weak derivatives up to order `k` exist and are in `L²_loc`:
`HasSobL2 (k+1) f` : `f ∈ L²_loc` and every first weak partial derivative `g` of `f` exists
with `HasSobL2 k g`.  Unfolded: every word `(i₁,…,i_j)`, `j ≤ k`, of iterated weak derivatives exists in `L²_loc`. -/
def HasSobL2 {d : ℕ} : ℕ → ((Fin d → ℝ) → ℝ) → Prop
  | 0, f => LocL2 f
  | k + 1, f => LocL2 f ∧ ∀ i : Fin d, ∃ g, WeakDeriv f g i ∧ HasSobL2 k g

/-- The `L¹_loc` variant (weaker hypothesis; the embedding is proved for this class). -/
def HasSobL1 {d : ℕ} : ℕ → ((Fin d → ℝ) → ℝ) → Prop
  | 0, f => LocallyIntegrable f
  | k + 1, f => LocallyIntegrable f ∧ ∀ i : Fin d, ∃ g, WeakDeriv f g i ∧ HasSobL1 k g

/-- partial derivative `∂_i φ = Dφ(·) e_i`. -/
noncomputable def pd {d : ℕ} (i : Fin d) (φ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => fderiv ℝ φ x (Pi.single i 1)

/-- iterated classical derivative: `iterD (i :: l) φ = ∂_i (iterD l φ)`. -/
noncomputable def iterD {d : ℕ} : List (Fin d) → ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ)
  | [], φ => φ
  | i :: l, φ => pd i (iterD l φ)

/-- iterated weak derivative along a word: `WeakIter (i :: l) f g` : `g = ∂_i h` weakly, `h = ∂_l f` weakly. -/
def WeakIter {d : ℕ} : List (Fin d) → ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) → Prop
  | [], f, g => f = g
  | i :: l, f, g => ∃ h, WeakIter l f h ∧ WeakDeriv h g i

theorem LocL2.locallyIntegrable {d : ℕ} {f : (Fin d → ℝ) → ℝ} (h : LocL2 f) : LocallyIntegrable f := by
  rw [locallyIntegrable_iff]
  intro K hK
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact (h K hK).integrable (by norm_num)

theorem HasSobL2.toL1 {d : ℕ} : ∀ (k : ℕ) {f : (Fin d → ℝ) → ℝ}, HasSobL2 k f → HasSobL1 k f
  | 0, _, h => LocL2.locallyIntegrable h
  | k + 1, _, h => ⟨h.1.locallyIntegrable, fun i => by
      obtain ⟨g, hg, hg2⟩ := h.2 i
      exact ⟨g, hg, HasSobL2.toL1 k hg2⟩⟩

theorem HasSobL1.mono {d : ℕ} : ∀ (k : ℕ) {f : (Fin d → ℝ) → ℝ}, HasSobL1 (k+1) f → HasSobL1 k f
  | 0, _, h => h.1
  | k + 1, _, h => ⟨h.1, fun i => by
      obtain ⟨g, hg, hg2⟩ := h.2 i
      exact ⟨g, hg, HasSobL1.mono k hg2⟩⟩

theorem HasSobL1.locallyIntegrable {d : ℕ} : ∀ (k : ℕ) {f : (Fin d → ℝ) → ℝ}, HasSobL1 k f →
    LocallyIntegrable f
  | 0, _, h => h
  | _ + 1, _, h => h.1

theorem contDiff_pd {d : ℕ} (i : Fin d) {φ : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (pd i φ) :=
  (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_iterD {d : ℕ} (l : List (Fin d)) {φ : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (iterD l φ) := by
  induction l with
  | nil => exact h
  | cons i l ih => exact contDiff_pd i ih

theorem hasCompactSupport_pd {d : ℕ} (i : Fin d) {φ : (Fin d → ℝ) → ℝ} (h : HasCompactSupport φ) :
    HasCompactSupport (pd i φ) :=
  h.fderiv_apply (𝕜 := ℝ) _

theorem hasCompactSupport_iterD {d : ℕ} (l : List (Fin d)) {φ : (Fin d → ℝ) → ℝ}
    (h : HasCompactSupport φ) : HasCompactSupport (iterD l φ) := by
  induction l with
  | nil => exact h
  | cons i l ih => exact hasCompactSupport_pd i ih

end MarkovTriple.BGL.Instances.GibbsRd.Sob
