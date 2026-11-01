import Mathlib
import MarkovTriple.Hilbert.SpectralGap

/-!
# Beurling–Deny: invariance of closed cones under the Friedrichs semigroup

Abstract form of the first Beurling–Deny criterion, stated on the Friedrichs form `(E, Q)`.
Let `Tm : H → H` be a "normal contraction" in the following sense:

* (`hQ`) `Tm` maps `Q` into `Q` and does not increase the closed form `E`;
* (`hnorm`) `Tm` does not increase the norm;
* (`hpair`) `⟪g, Tm u - u⟫ ≥ 0` for `g` in a closed cone `C` (for `Tm = |·|` on `L²`, `C = {g ≥ 0}`);
* (`hfix`) fixed points of `Tm` belong to `C` (`|u| = u ⇒ u ≥ 0`).

Then every resolvent `λ R_λ` (`λ > 0`) and hence the whole semigroup `P_t` maps `C` to `C`.

This is the Q-level restatement of `fixed_of_comparison` of `cutoff-rigidity-diffusions`
(`DiffMarkov.lean`, the second copy of the form structure `DirFormData`), made available directly
on the single `FormData` structure.
-/

open Filter Topology Set
open scoped NNReal InnerProductSpace

set_option linter.unusedSectionVars false

namespace MarkovTriple.Hilbert

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- Beurling–Deny comparison at the level of the resolvent: `R_λ g` is fixed by `Tm`. -/
theorem resolvent_fixed_of_comparison (Tm : H → H)
    (hQ : ∀ u : S.Q, ∃ v : S.Q, (v : H) = Tm u ∧ S.E v v ≤ S.E u u)
    (hnorm : ∀ u, ‖Tm u‖ ≤ ‖u‖) {lam : ℝ} (hlam : 0 < lam) (g : H)
    (hpair : 0 ≤ inner ℝ g (Tm (S.resolvent lam g) - S.resolvent lam g)) :
    Tm (S.resolvent lam g) = S.resolvent lam g := by
  set u : H := S.resolvent lam g with hu
  have huQ : u ∈ S.Q := S.resolvent_mem_Q hlam g
  set u' : S.Q := ⟨u, huQ⟩ with hu'
  obtain ⟨φ', hφ, hEφ⟩ := hQ u'
  set φ : H := Tm u with hφdef
  have hweak : ∀ ψ : S.Q, S.E u' ψ + lam * inner ℝ u (ψ : H) = inner ℝ g (ψ : H) :=
    fun ψ => S.E_resolvent hlam g ψ
  have h1 : S.E u' φ' + lam * inner ℝ u φ = inner ℝ g φ := by
    have := hweak φ'; rw [hφ] at this; exact this
  have h2 : S.E u' u' + lam * ‖u‖ ^ 2 = inner ℝ g u := by
    have := hweak u'
    change S.E u' u' + lam * inner ℝ u u = inner ℝ g u at this
    rwa [real_inner_self_eq_norm_sq] at this
  have hexp : S.E (φ' - (1 : ℝ) • u') (φ' - (1 : ℝ) • u') =
      S.E φ' φ' - 2 * 1 * S.E φ' u' + 1 ^ 2 * S.E u' u' := S.E_sub_smul_self φ' u' 1
  have hnn := S.E_nonneg (φ' - (1 : ℝ) • u')
  have hcomm : S.E φ' u' = S.E u' φ' := by
    simp only [FormData.E, FormData.E1]
    rw [real_inner_comm (S.qEquiv.symm φ'), real_inner_comm (φ' : H)]
  rw [hexp, hcomm] at hnn
  have hnexp : ‖φ - u‖ ^ 2 = ‖φ‖ ^ 2 - 2 * inner ℝ u φ + ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm φ u]
    ring
  have h3 : ‖φ‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have := hnorm u
    have := norm_nonneg φ
    nlinarith
  have hpos' : 0 ≤ inner ℝ g φ - inner ℝ g u := by
    rw [inner_sub_right] at hpair; exact hpair
  have : lam * ‖φ - u‖ ^ 2 ≤ 0 := by
    rw [hnexp]
    nlinarith
  have hn : ‖φ - u‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have : ‖φ - u‖ = 0 := by
    have := sq_nonneg ‖φ - u‖
    nlinarith [norm_nonneg (φ - u)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Beurling–Deny.** Under the hypotheses above, `P_t` preserves the closed cone `C`. -/
theorem semigroup_mapsTo_of_contraction (Tm : H → H) (C : Set H) (hC : IsClosed C)
    (hcone : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ C, c • x ∈ C)
    (hQ : ∀ u : S.Q, ∃ v : S.Q, (v : H) = Tm u ∧ S.E v v ≤ S.E u u)
    (hnorm : ∀ u, ‖Tm u‖ ≤ ‖u‖)
    (hpair : ∀ g ∈ C, ∀ u, 0 ≤ inner ℝ g (Tm u - u))
    (hfix : ∀ u, Tm u = u → u ∈ C) (t : ℝ≥0) {g : H} (hg : g ∈ C) :
    S.semigroup t g ∈ C := by
  refine S.semigroup_mapsTo C hC (fun lam hlam x hx => ?_) t hg
  have hfx := S.resolvent_fixed_of_comparison Tm hQ hnorm hlam x (hpair x hx _)
  exact hcone lam hlam.le _ (hfix _ hfx)

end FormData

end MarkovTriple.Hilbert
