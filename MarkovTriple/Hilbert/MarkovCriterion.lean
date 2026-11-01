import Mathlib
import MarkovTriple.Hilbert.DirBridge
import MarkovTriple.Hilbert.Bridge

/-!
# A checkable-on-the-core sufficient condition for the Markov property of the form

(Uses the merged `closed_of_bounded` lower-semicontinuity argument ported from
`cutoff-rigidity-diffusions/DiffMarkov.lean`.)

* `FormData.exists_contraction_of_approx`: if a Lipschitz map `Tm` can be approximated on the core
  `D` -- for every `f ∈ D` and `ε > 0` there is `g ∈ D` with `‖g - Tm f‖ < ε` and
  `en g ≤ en f + ε` -- then `Tm` maps the form domain `Q` to itself and does not increase `E`.
* `isMarkovianForm_of_approx`: for a Markov triple, the same for `Tm = |·|` on `L²(μ)` (the
  hypothesis is the usual smooth-truncation approximation `ψ_ε(f) ∈ 𝒜₀`, `ψ_ε → |·|`, which holds
  e.g. whenever `𝒜₀` is stable under a family of smooth approximations of `|·|`), giving
  `IsMarkovianForm T`.
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

end FormData

variable {E : Type*} [MeasurableSpace E] (T : _root_.MarkovTriple E)

lemma lipschitz_abs (u v : Lp ℝ 2 T.μ) : ‖|u| - |v|‖ ≤ 1 * ‖u - v‖ := by
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub |u| |v|, Lp.coeFn_abs u, Lp.coeFn_abs v, Lp.coeFn_sub u v]
    with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_abs_sub_abs_le_abs_sub _ _

/-- **Sufficient condition for `IsMarkovianForm`** (approximation of `|f|` on the core `𝒜₀` with
no energy increase). -/
theorem isMarkovianForm_of_approx
    (h : ∀ f : T.A₀, ∀ ε > 0, ∃ g : T.A₀,
      ‖toLp0 T g - |toLp0 T f|‖ < ε ∧ qf T g g ≤ qf T f f + ε) : IsMarkovianForm T := by
  intro u
  refine (formData T).exists_contraction_of_approx (fun w => |w|) 1 (lipschitz_abs T) ?_ u
  intro f ε hε
  obtain ⟨_, f', rfl⟩ := f
  obtain ⟨g', hg1, hg2⟩ := h f' ε hε
  refine ⟨⟨toLp0 T g', ⟨g', rfl⟩⟩, hg1, ?_⟩
  have e1 : (formData T).en ⟨toLp0 T g', ⟨g', rfl⟩⟩ ⟨toLp0 T g', ⟨g', rfl⟩⟩ = qf T g' g' :=
    inner_formA T g' g'
  have e2 : (formData T).en ⟨toLp0 T f', ⟨f', rfl⟩⟩ ⟨toLp0 T f', ⟨f', rfl⟩⟩ = qf T f' f' :=
    inner_formA T f' f'
  rw [e1, e2]; exact hg2

end MarkovTriple.Hilbert
