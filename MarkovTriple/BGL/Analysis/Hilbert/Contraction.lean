import Mathlib
import MarkovTriple.BGL.Analysis.Hilbert.DirBridge
import MarkovTriple.BGL.Analysis.Hilbert.BeurlingDeny

/-!
# Contraction criterion on the core and the resolvent pairing inequality

Ported (statements unchanged) from the legacy `Hilbert/MarkovCriterion.lean`
(`FormData.exists_contraction_of_approx`: a Lipschitz map `Tm` approximable on the core `D` by
`g` with `‖g - Tm f‖ < ε`, `en g ≤ en f + ε` maps `Q` to itself and does not increase `E`) and
`Hilbert/SubMarkov.lean` (`FormData.resolvent_pairing_nonpos`).  Used by `BGL/Semigroup/Markov.lean`.
-/

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

theorem exists_contraction_of_approx (Tm : H → H) (L : ℝ)
    (hL : ∀ u v, ‖Tm u - Tm v‖ ≤ L * ‖u - v‖)
    (happrox : ∀ f : S.D, ∀ ε > 0, ∃ g : S.D, ‖(g : H) - Tm f‖ < ε ∧ S.en g g ≤ S.en f f + ε)
    (u : S.Q) : ∃ v : S.Q, (v : H) = Tm u ∧ S.E v v ≤ S.E u u := by
  classical
  set T := S.dirFriedrichs with hT
  have huT : (u : H) ∈ T.Q := u.2
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 huT
  have hg : ∀ n : ℕ, ∃ g : S.D, ‖(g : H) - Tm (f n)‖ < 1 / ((n : ℝ) + 1) ∧
      S.en g g ≤ S.en (f n) (f n) + 1 / ((n : ℝ) + 1) := fun n =>
    happrox (f n) _ (by positivity)
  choose g hg1 hg2 using hg
  have hgt : Tendsto (fun n => (g n : H)) atTop (𝓝 (Tm u)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n => ‖(f n : H) - u‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hf
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) + L * ‖(f n : H) - u‖) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add (h0.const_mul L)
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
    calc ‖(g n : H) - Tm u‖ = ‖((g n : H) - Tm (f n)) + (Tm (f n) - Tm u)‖ := by congr 1; abel
      _ ≤ ‖(g n : H) - Tm (f n)‖ + ‖Tm (f n) - Tm u‖ := norm_add_le _ _
      _ ≤ 1 / ((n : ℝ) + 1) + L * ‖(f n : H) - u‖ := add_le_add (hg1 n).le (hL _ _)
  have hlim := T.E_lim f f u u hf hfc hf hfc
  have hbound : ∀ ε > 0, T.E (Tm u) (Tm u) ≤ T.E u u + ε ∧ Tm u ∈ T.Q := by
    intro ε hε
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hlim.eventually (Iio_mem_nhds
      (show T.E u u < T.E u u + ε / 2 by linarith)))
    obtain ⟨N2, hN2⟩ := exists_nat_gt (2 / ε)
    have := T.closed_of_bounded (fun k => g (k + max N1 N2)) (Tm u)
      (hgt.comp (tendsto_add_atTop_nat (max N1 N2))) (T.E u u + ε) (fun k => by
        have h1 := hg2 (k + max N1 N2)
        have h2 := hN1 (k + max N1 N2) (le_trans (le_max_left _ _) (Nat.le_add_left _ _))
        have h3 : 1 / (((k + max N1 N2 : ℕ) : ℝ) + 1) ≤ ε / 2 := by
          have hpos : (0 : ℝ) < ((k + max N1 N2 : ℕ) : ℝ) + 1 := by positivity
          rw [div_le_iff₀ hpos]
          have : (N2 : ℝ) ≤ ((k + max N1 N2 : ℕ) : ℝ) := by
            exact_mod_cast le_trans (le_max_right _ _) (Nat.le_add_left _ _)
          have h4 : 2 / ε < (k + max N1 N2 : ℕ) + 1 := by linarith
          rw [div_lt_iff₀ hε] at h4
          nlinarith
        linarith)
    exact ⟨this.2, this.1⟩
  have hmem : Tm u ∈ T.Q := (hbound 1 one_pos).2
  refine ⟨⟨Tm u, hmem⟩, rfl, ?_⟩
  have e1 : T.E (Tm u) (Tm u) ≤ T.E u u :=
    le_of_forall_pos_le_add fun ε hε => (hbound ε hε).1
  have hE : ∀ (a b : H) (ha : a ∈ S.Q) (hb : b ∈ S.Q), T.E a b = S.E ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b ha hb
    show (if h : a ∈ S.Q ∧ b ∈ S.Q then S.E ⟨a, h.1⟩ ⟨b, h.2⟩ else 0) = _
    rw [dif_pos (show a ∈ S.Q ∧ b ∈ S.Q from ⟨ha, hb⟩)]
  rw [hE _ _ hmem hmem, hE _ _ u.2 u.2] at e1
  exact e1

/-- Resolvent pairing inequality for a map `Tm` not increasing the closed form. -/
theorem resolvent_pairing_nonpos (Tm : H → H)
    (hQ : ∀ u : S.Q, ∃ v : S.Q, (v : H) = Tm u ∧ S.E v v ≤ S.E u u)
    {lam : ℝ} (hlam : 0 < lam) (g : H) :
    inner ℝ (g - lam • S.resolvent lam g) (Tm (S.resolvent lam g) - S.resolvent lam g) ≤ 0 := by
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
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    real_inner_self_eq_norm_sq]
  simp only [conj_trivial]
  nlinarith


end FormData

end MarkovTriple.Hilbert
