import Mathlib
import MarkovTriple.Hilbert.DirBridge
import MarkovTriple.Hilbert.Bridge
import MarkovTriple.Frozen.PartialDeriv

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
* `isMarkovianForm` (NEW, ERRATA F5/H2): for **every** `MarkovTriple`, `IsMarkovianForm T` is a
  theorem.  `𝒜₀` is stable under `ψ_δ(t) = √(t²+δ²) − δ` (`ψ_δ(0) = 0`, `comp_mem`), the chain rule
  gives `Γ(ψ_δ f) = ψ_δ'(f)² Γ(f) ≤ Γ(f)` (`|ψ_δ'| ≤ 1`), and `ψ_δ(f) → |f|` in `L²` by dominated
  convergence (`0 ≤ |f| − ψ_δ(f) ≤ min(δ,|f|)`).  Plugged into `isMarkovianForm_of_approx`.
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

section Truncation

noncomputable def trunc (δ : ℝ) (z : Fin 1 → ℝ) : ℝ := √(z 0 ^ 2 + δ ^ 2) - δ

lemma contDiff_trunc {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ (⊤ : ℕ∞) (trunc δ) := by
  unfold trunc
  refine ContDiff.sub ?_ contDiff_const
  refine ContDiff.sqrt ?_ (fun z => by positivity)
  exact ((contDiff_apply ℝ ℝ 0).pow 2).add contDiff_const

lemma trunc_zero {δ : ℝ} (hδ : 0 < δ) : trunc δ 0 = 0 := by
  simp [trunc, Real.sqrt_sq hδ.le]

lemma pderiv_trunc {δ : ℝ} (hδ : 0 < δ) (z : Fin 1 → ℝ) :
    MarkovTriple.pderiv (trunc δ) 0 z = z 0 / √(z 0 ^ 2 + δ ^ 2) := by
  have hpos : 0 < z 0 ^ 2 + δ ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => √(t ^ 2 + δ ^ 2) - δ) (z 0 / √(z 0 ^ 2 + δ ^ 2)) (z 0) := by
    have := ((((hasDerivAt_id (z 0)).pow 2).add_const (δ ^ 2)).sqrt hpos.ne').sub_const δ
    refine this.congr_deriv ?_
    have : 0 < √(z 0 ^ 2 + δ ^ 2) := Real.sqrt_pos.2 hpos
    simp only [id, Pi.pow_apply]
    field_simp
    norm_num
  have h2 := h1.comp_hasFDerivAt z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  unfold MarkovTriple.pderiv
  have h3 : fderiv ℝ (trunc δ) z = _ := h2.fderiv
  rw [h3]
  simp

lemma abs_pderiv_trunc_le {δ : ℝ} (hδ : 0 < δ) (z : Fin 1 → ℝ) :
    |MarkovTriple.pderiv (trunc δ) 0 z| ≤ 1 := by
  rw [pderiv_trunc hδ, abs_div, abs_of_pos (Real.sqrt_pos.2 (by positivity : 0 < z 0 ^ 2 + δ ^ 2))]
  rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
  calc |z 0| = √(z 0 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])

lemma trunc_bounds {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ |t| - (√(t ^ 2 + δ ^ 2) - δ) ∧ |t| - (√(t ^ 2 + δ ^ 2) - δ) ≤ min δ |t| := by
  have h1 : |t| ≤ √(t ^ 2 + δ ^ 2) := by
    calc |t| = √(t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
  have h2 : √(t ^ 2 + δ ^ 2) ≤ |t| + δ := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_abs t, abs_nonneg t]
  have h3 : δ ≤ √(t ^ 2 + δ ^ 2) := by
    calc δ = √(δ ^ 2) := (Real.sqrt_sq hδ.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  refine ⟨by linarith, le_min (by linarith) (by linarith)⟩



lemma exists_small_min (f : E → ℝ) (hf : MemLp f 2 T.μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∫ x, (min δ |f x|) ^ 2 ∂T.μ < ε := by
  have hint : Integrable (fun x => f x ^ 2) T.μ := hf.integrable_sq
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ x, (min (1 / ((n:ℝ)+1)) |f x|) ^ 2 ∂T.μ)
      Filter.atTop (nhds 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := T.μ) (fun x => f x ^ 2)
      (F := fun (n : ℕ) x => (min (1 / ((n:ℝ)+1)) |f x|) ^ 2) (f := fun _ => (0:ℝ))
      (fun n => by
        exact ((aemeasurable_const.min hf.aemeasurable.norm).pow_const 2).aestronglyMeasurable)
      hint
      (fun n => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h0 : 0 ≤ min (1 / ((n:ℝ)+1)) |f x| := le_min (by positivity) (abs_nonneg _)
        have h1 : min (1 / ((n:ℝ)+1)) |f x| ≤ |f x| := min_le_right _ _
        calc _ ≤ |f x| ^ 2 := by gcongr
          _ = f x ^ 2 := sq_abs _)
      (Filter.Eventually.of_forall fun x => by
        have h : Filter.Tendsto (fun n : ℕ => min (1 / ((n:ℝ)+1)) |f x|) Filter.atTop (nhds 0) := by
          refine squeeze_zero (fun n => le_min (by positivity) (abs_nonneg _)) (fun n => min_le_left _ _)
            tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using h.pow 2)
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨1 / ((n:ℝ)+1), by positivity, hn⟩


lemma integrable_min_sq (f : E → ℝ) (hf : MemLp f 2 T.μ) (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun x => (min δ |f x|) ^ 2) T.μ := by
  refine hf.integrable_sq.mono' ((aemeasurable_const.min hf.aemeasurable.norm).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ min δ |f x| := le_min hδ.le (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc _ ≤ |f x| ^ 2 := by gcongr; exact min_le_right _ _
    _ = f x ^ 2 := sq_abs _

/-- **The Markov property of the form is a theorem** for every `MarkovTriple`: `𝒜₀` is stable under
the smooth truncations `ψ_δ(f) = √(f²+δ²) − δ` (`ψ_δ(0) = 0`), `Γ(ψ_δ f) = ψ_δ'(f)² Γ(f) ≤ Γ(f)`
by the chain rule, and `ψ_δ(f) → |f|` in `L²` (dominated convergence). -/
theorem isMarkovianForm : IsMarkovianForm T := by
  apply isMarkovianForm_of_approx
  intro f ε hε
  obtain ⟨δ, hδ, hint⟩ := exists_small_min T f.1 (memLp2 T f.2) (pow_pos hε 2)
  set g : E → ℝ := fun x => trunc δ (fun _ => f.1 x) with hg
  have hgmem : g ∈ T.A₀ := T.comp_mem 1 (trunc δ) (contDiff_trunc hδ) (trunc_zero hδ)
    (fun _ => f.1) (fun _ => f.2)
  have hΓ := (T.diffusion 1 (trunc δ) (contDiff_trunc hδ) (trunc_zero hδ)
    (fun _ => f.1) (fun _ => f.2)).1
  refine ⟨⟨g, hgmem⟩, ?_, ?_⟩
  · set v : Lp ℝ 2 T.μ := toLp0 T ⟨g, hgmem⟩ - |toLp0 T f| with hv
    have e : ‖v‖ ^ 2 = ∫ x, (g x - |f.1 x|) ^ 2 ∂T.μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (toLp0 T ⟨g, hgmem⟩) |toLp0 T f|, coeFn_toLp0 T ⟨g, hgmem⟩,
        coeFn_toLp0 T f, Lp.coeFn_abs (toLp0 T f)] with x h1 h2 h3 h4
      rw [hv, h1, Pi.sub_apply, h2, h4, h3]
      simp [sq]
    have hle : ∫ x, (g x - |f.1 x|) ^ 2 ∂T.μ ≤ ∫ x, (min δ |f.1 x|) ^ 2 ∂T.μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        (integrable_min_sq T f.1 (memLp2 T f.2) δ hδ) (Filter.Eventually.of_forall fun x => ?_)
      obtain ⟨h0, h1⟩ := trunc_bounds hδ (f.1 x)
      have : g x - |f.1 x| = -(|f.1 x| - (√(f.1 x ^ 2 + δ ^ 2) - δ)) := by
        simp only [hg, trunc]; ring
      show (g x - |f.1 x|) ^ 2 ≤ (min δ |f.1 x|) ^ 2
      rw [this, neg_sq]
      exact pow_le_pow_left₀ h0 h1 2
    have : ‖v‖ ^ 2 < ε ^ 2 := by rw [e]; exact lt_of_le_of_lt hle hint
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  · have key : ∀ x, T.Γ g g x = (MarkovTriple.pderiv (trunc δ) 0 (fun _ => f.1 x)) ^ 2 *
        T.Γ f.1 f.1 x := by
      intro x
      have h1 := congrFun (hΓ g hgmem) x
      have h2 := congrFun (hΓ f.1 f.2) x
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at h1 h2
      rw [h1, T.Γ_symm f.1 f.2 g hgmem, h2]; ring
    have hmono : ∫ x, T.Γ g g x ∂T.μ ≤ ∫ x, T.Γ f.1 f.1 x ∂T.μ := by
      refine integral_mono (Γ_integrable T ⟨g, hgmem⟩ ⟨g, hgmem⟩) (Γ_integrable T f f)
        (fun x => ?_)
      rw [key x]
      have hp : (MarkovTriple.pderiv (trunc δ) 0 (fun _ => f.1 x)) ^ 2 ≤ 1 := by
        have := abs_pderiv_trunc_le hδ (fun _ => f.1 x)
        nlinarith [sq_abs (MarkovTriple.pderiv (trunc δ) 0 (fun _ => f.1 x)), abs_nonneg (MarkovTriple.pderiv (trunc δ) 0 (fun _ => f.1 x))]
      nlinarith [T.Γ_nonneg f.1 f.2 x]
    have : qf T ⟨g, hgmem⟩ ⟨g, hgmem⟩ ≤ qf T f f := hmono
    linarith


end Truncation

end MarkovTriple.Hilbert
