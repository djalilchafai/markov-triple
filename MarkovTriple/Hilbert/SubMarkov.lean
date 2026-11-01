import Mathlib
import MarkovTriple.Hilbert.MarkovCriterion

/-!
# Second Beurling–Deny criterion: the Friedrichs semigroup is sub-Markov

For every `MarkovTriple` `T` (no extra hypothesis) and `u ∈ L²(μ)` with `u ≤ 1` a.e.,
`P_t u ≤ 1` a.e. (`tripleSemigroup_subMarkov`).  ERRATA N2.

Proof.
* (`resolvent_pairing_nonpos`) for the Friedrichs form `(E, Q)`, any `Tm : Q → Q` which does not
  increase `E` satisfies `⟪g − λ R_λ g, Tm(R_λ g) − R_λ g⟫ ≤ 0`.
* The clip `Tm_c u = u ∧ c` (`c > 0`) does not increase `E` (`isClipForm`): it is approximated in
  `L²` by `ψ_δ(f)`, `f ∈ 𝒜₀`, where `ψ_δ(t) = (t − √((t−c)²+δ²) + √(c²+δ²))/2` is smooth with
  `ψ_δ(0) = 0`, `0 ≤ ψ_δ' ≤ 1`, `ψ_δ → t ∧ c`; `ψ_δ(f) ∈ 𝒜₀` by `comp_mem` and
  `Γ(ψ_δ f) = ψ_δ'(f)² Γ(f) ≤ Γ(f)` by `diffusion` (same machinery as `isMarkovianForm`).
* If `g ≤ 1`, then `λ R_λ g ≤ 1` (take `c = 1/λ`), hence the closed set `{w ≤ 1}` is invariant
  under the semigroup (`FormData.semigroup_mapsTo`).
-/

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

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

section Clip

variable {E : Type*} [MeasurableSpace E] (T : _root_.MarkovTriple E)

lemma abs_min_le (a c : ℝ) (hc : 0 ≤ c) : |min a c| ≤ |a| := by
  rcases le_total a c with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_of_nonneg hc]; exact h.trans (le_abs_self a)

lemma memLp_clip (c : ℝ) (hc : 0 ≤ c) (u : Lp ℝ 2 T.μ) :
    MemLp (fun x => min (u x) c) 2 T.μ := by
  refine (Lp.memLp u).of_le
    (((Lp.aestronglyMeasurable u).aemeasurable.min aemeasurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs] using abs_min_le (u x) c hc

/-- The clip `u ↦ u ∧ c` on `L²(μ)` (`c ≥ 0`). -/
noncomputable def clip (c : ℝ) (hc : 0 ≤ c) (u : Lp ℝ 2 T.μ) : Lp ℝ 2 T.μ :=
  (memLp_clip T c hc u).toLp _

lemma coeFn_clip (c : ℝ) (hc : 0 ≤ c) (u : Lp ℝ 2 T.μ) :
    (clip T c hc u : E → ℝ) =ᵐ[T.μ] fun x => min (u x) c :=
  MemLp.coeFn_toLp _

lemma lipschitz_clip (c : ℝ) (hc : 0 ≤ c) (u v : Lp ℝ 2 T.μ) :
    ‖clip T c hc u - clip T c hc v‖ ≤ 1 * ‖u - v‖ := by
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (clip T c hc u) (clip T c hc v), coeFn_clip T c hc u,
    coeFn_clip T c hc v, Lp.coeFn_sub u v] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  have := abs_min_sub_min_le_max (u x) c (v x) c
  simpa using this

/-- Smooth approximation of `t ↦ t ∧ c`. -/
noncomputable def clipFn (c δ : ℝ) (z : Fin 1 → ℝ) : ℝ :=
  (z 0 - √((z 0 - c) ^ 2 + δ ^ 2) + √(c ^ 2 + δ ^ 2)) / 2

lemma contDiff_clipFn {δ : ℝ} (hδ : 0 < δ) (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (clipFn c δ) := by
  unfold clipFn
  refine ContDiff.div_const (ContDiff.add (ContDiff.sub (contDiff_apply ℝ ℝ 0) ?_)
    contDiff_const) 2
  refine ContDiff.sqrt ?_ (fun z => by positivity)
  exact (((contDiff_apply ℝ ℝ 0).sub contDiff_const).pow 2).add contDiff_const

lemma clipFn_zero (c δ : ℝ) : clipFn c δ 0 = 0 := by
  simp [clipFn]

lemma pderiv_clipFn {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (z : Fin 1 → ℝ) :
    MarkovTriple.pderiv (clipFn c δ) 0 z =
      (1 - (z 0 - c) / √((z 0 - c) ^ 2 + δ ^ 2)) / 2 := by
  have hpos : 0 < (z 0 - c) ^ 2 + δ ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (t - √((t - c) ^ 2 + δ ^ 2) + √(c ^ 2 + δ ^ 2)) / 2)
      ((1 - (z 0 - c) / √((z 0 - c) ^ 2 + δ ^ 2)) / 2) (z 0) := by
    have h := ((((hasDerivAt_id (z 0)).sub_const c).pow 2).add_const (δ ^ 2)).sqrt hpos.ne'
    have h' := (((hasDerivAt_id (z 0)).sub h).add_const (√(c ^ 2 + δ ^ 2))).div_const 2
    refine h'.congr_deriv ?_
    have : 0 < √((z 0 - c) ^ 2 + δ ^ 2) := Real.sqrt_pos.2 hpos
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  have h2 := h1.comp_hasFDerivAt z
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  unfold MarkovTriple.pderiv
  have h3 : fderiv ℝ (clipFn c δ) z = _ := h2.fderiv
  rw [h3]
  simp

lemma abs_pderiv_clipFn_le {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (z : Fin 1 → ℝ) :
    |MarkovTriple.pderiv (clipFn c δ) 0 z| ≤ 1 := by
  rw [pderiv_clipFn hδ]
  have hApos : 0 < √((z 0 - c) ^ 2 + δ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hr : |(z 0 - c) / √((z 0 - c) ^ 2 + δ ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hApos, div_le_one hApos]
    calc |z 0 - c| = √((z 0 - c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
  obtain ⟨h1, h2⟩ := abs_le.1 hr
  rw [abs_le]
  constructor <;> linarith

lemma abs_sqrt_sub_sqrt_le (x y δ : ℝ) :
    |√(x ^ 2 + δ ^ 2) - √(y ^ 2 + δ ^ 2)| ≤ |x - y| := by
  set X := √(x ^ 2 + δ ^ 2) with hX
  set Y := √(y ^ 2 + δ ^ 2) with hY
  have hX2 : X ^ 2 = x ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  have hY2 : Y ^ 2 = y ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hXY : δ ^ 2 + x * y ≤ X * Y := by
    by_cases h : δ ^ 2 + x * y ≤ 0
    · exact h.trans (mul_nonneg hX0 hY0)
    · push Not at h
      apply le_of_sq_le_sq _ (mul_nonneg hX0 hY0)
      · rw [mul_pow, hX2, hY2]; nlinarith [sq_nonneg (δ * (x - y))]
  apply sq_le_sq.1
  nlinarith

lemma clipFn_bounds {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    |clipFn c δ (fun _ => t)| ≤ |t| ∧ |clipFn c δ (fun _ => t) - min t c| ≤ δ := by
  have hpos : 0 ≤ (t - c) ^ 2 + δ ^ 2 := by positivity
  set A := √((t - c) ^ 2 + δ ^ 2) with hA
  set B := √(c ^ 2 + δ ^ 2) with hB
  have hAB : |A - B| ≤ |t| := by
    have := abs_sqrt_sub_sqrt_le (t - c) (-c) δ
    rw [neg_sq] at this
    simpa [hA, hB] using this
  have hA1' : |t - c| ≤ A := by
    have := (trunc_bounds hδ (t - c)).2; have := min_le_left δ |t - c|; linarith
  have hA2' : A ≤ |t - c| + δ := by
    have := (trunc_bounds hδ (t - c)).1; linarith
  have hB1' : c ≤ B := by
    have := (trunc_bounds hδ c).2; have := min_le_left δ |c|
    rw [abs_of_nonneg hc] at *; linarith
  have hB2' : B ≤ c + δ := by
    have := (trunc_bounds hδ c).1; rw [abs_of_nonneg hc] at *; linarith
  have hd : clipFn c δ (fun _ => t) = (t - A + B) / 2 := rfl
  rw [hd]
  obtain ⟨h1, h2⟩ := abs_le.1 hAB
  constructor
  · rw [abs_le]
    constructor <;> nlinarith [neg_abs_le t, le_abs_self t]
  · rcases le_total t c with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith : t - c ≤ 0)] at *
      rw [abs_le]; constructor <;> linarith
    · rw [min_eq_right h, abs_of_nonneg (by linarith : 0 ≤ t - c)] at *
      rw [abs_le]; constructor <;> linarith

/-- Composition with a smooth `ψ`, `ψ(0)=0`, `|ψ'| ≤ 1` stays in `𝒜₀` and does not increase the
energy (chain rule). -/
lemma comp_qf_le {ψ : (Fin 1 → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (hb : ∀ z, |MarkovTriple.pderiv ψ 0 z| ≤ 1) (f : T.A₀) :
    ∃ hg : (fun x => ψ (fun _ => f.1 x)) ∈ T.A₀,
      qf T ⟨_, hg⟩ ⟨_, hg⟩ ≤ qf T f f := by
  set g : E → ℝ := fun x => ψ (fun _ => f.1 x) with hg
  have hgmem : g ∈ T.A₀ := T.comp_mem 1 ψ hψ h0 (fun _ => f.1) (fun _ => f.2)
  have hΓ := (T.diffusion 1 ψ hψ h0 (fun _ => f.1) (fun _ => f.2)).1
  refine ⟨hgmem, ?_⟩
  have key : ∀ x, T.Γ g g x = (MarkovTriple.pderiv ψ 0 (fun _ => f.1 x)) ^ 2 *
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
    have hp : (MarkovTriple.pderiv ψ 0 (fun _ => f.1 x)) ^ 2 ≤ 1 := by
      have := hb (fun _ => f.1 x)
      nlinarith [sq_abs (MarkovTriple.pderiv ψ 0 (fun _ => f.1 x)),
        abs_nonneg (MarkovTriple.pderiv ψ 0 (fun _ => f.1 x))]
    nlinarith [T.Γ_nonneg f.1 f.2 x]
  exact hmono

/-- **The clip `u ↦ u ∧ c` is a normal contraction for the closed form**: for every `u ∈ Q`,
`u ∧ c ∈ Q` and `ℰ(u ∧ c) ≤ ℰ(u)` (`c > 0`). -/
theorem isClipForm {c : ℝ} (hc : 0 < c) : ∀ u : (formData T).Q, ∃ v : (formData T).Q,
    (v : Lp ℝ 2 T.μ) = clip T c hc.le u ∧ (formData T).E v v ≤ (formData T).E u u := by
  intro u
  refine (formData T).exists_contraction_of_approx (clip T c hc.le) 1
    (lipschitz_clip T c hc.le) ?_ u
  intro f ε hε
  obtain ⟨_, f', rfl⟩ := f
  obtain ⟨δ, hδ, hint⟩ := exists_small_min T f'.1 (memLp2 T f'.2) (pow_pos (half_pos hε) 2)
  obtain ⟨hg, hq⟩ := comp_qf_le T (contDiff_clipFn hδ c) (clipFn_zero c δ)
    (abs_pderiv_clipFn_le hδ c) f'
  set g : E → ℝ := fun x => clipFn c δ (fun _ => f'.1 x) with hgdef
  refine ⟨⟨toLp0 T ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩, ?_, ?_⟩
  · have e : ‖toLp0 T ⟨g, hg⟩ - clip T c hc.le (toLp0 T f')‖ ^ 2 =
        ∫ x, (g x - min (f'.1 x) c) ^ 2 ∂T.μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (toLp0 T ⟨g, hg⟩) (clip T c hc.le (toLp0 T f')),
        coeFn_toLp0 T ⟨g, hg⟩, coeFn_clip T c hc.le (toLp0 T f'), coeFn_toLp0 T f']
        with x h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3, h4]
      simp [sq]
    have hle : ∫ x, (g x - min (f'.1 x) c) ^ 2 ∂T.μ ≤
        ∫ x, 4 * (min δ |f'.1 x|) ^ 2 ∂T.μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        ((integrable_min_sq T f'.1 (memLp2 T f'.2) δ hδ).const_mul 4)
        (Filter.Eventually.of_forall fun x => ?_)
      obtain ⟨b1, b2⟩ := clipFn_bounds hδ hc.le (f'.1 x)
      have b3 := abs_min_le (f'.1 x) c hc.le
      have hd1 : |g x - min (f'.1 x) c| ≤ 2 * min δ |f'.1 x| := by
        rcases le_total δ |f'.1 x| with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]
          calc |g x - min (f'.1 x) c| ≤ |g x| + |min (f'.1 x) c| := abs_sub _ _
            _ ≤ _ := by linarith
      show (g x - min (f'.1 x) c) ^ 2 ≤ 4 * (min δ |f'.1 x|) ^ 2
      calc (g x - min (f'.1 x) c) ^ 2 = |g x - min (f'.1 x) c| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * min δ |f'.1 x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd1 2
        _ = 4 * (min δ |f'.1 x|) ^ 2 := by ring
    have h4 : ∫ x, 4 * (min δ |f'.1 x|) ^ 2 ∂T.μ = 4 * ∫ x, (min δ |f'.1 x|) ^ 2 ∂T.μ :=
      integral_const_mul _ _
    have : ‖toLp0 T ⟨g, hg⟩ - clip T c hc.le (toLp0 T f')‖ ^ 2 < ε ^ 2 := by
      rw [e]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  · have e1 : (formData T).en ⟨toLp0 T ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩ ⟨toLp0 T ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩ =
        qf T ⟨g, hg⟩ ⟨g, hg⟩ := inner_formA T ⟨g, hg⟩ ⟨g, hg⟩
    have e2 : (formData T).en ⟨toLp0 T f', ⟨f', rfl⟩⟩ ⟨toLp0 T f', ⟨f', rfl⟩⟩ = qf T f' f' :=
      inner_formA T f' f'
    rw [e1, e2]; linarith

lemma isClosed_ae_le_one (μ : Measure E) :
    IsClosed {w : Lp ℝ 2 μ | (w : E → ℝ) ≤ᵐ[μ] (1 : E → ℝ)} := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨s, hs, hsw⟩ := mem_closure_iff_seq_limit.1 hw
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hsw).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, (s n : E → ℝ) x ≤ 1 := ae_all_iff.2 fun n => hs n
  filter_upwards [hae, hall] with x h1 h2
  exact le_of_tendsto' h1 (fun i => h2 (ns i))

/-- **Resolvent estimate**: `g ≤ 1` a.e. implies `λ R_λ g ≤ 1` a.e. -/
theorem resolvent_le_one (g : Lp ℝ 2 T.μ) (hg : (g : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ))
    {lam : ℝ} (hlam : 0 < lam) :
    (((lam • (formData T).resolvent lam) g : Lp ℝ 2 T.μ) : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ) := by
  set S := formData T with hS
  set u : Lp ℝ 2 T.μ := S.resolvent lam g with hu
  have hc : 0 < lam⁻¹ := inv_pos.2 hlam
  set a : Lp ℝ 2 T.μ := g - lam • u with ha
  set w : Lp ℝ 2 T.μ := clip T lam⁻¹ hc.le u - u with hw
  have hpair := S.resolvent_pairing_nonpos (clip T lam⁻¹ hc.le)
    (isClipForm T hc) hlam g
  change inner ℝ a w ≤ 0 at hpair
  have hinner : inner ℝ a w = ∫ x, a x * w x ∂T.μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_comm]
  have hInt : Integrable (fun x => a x * w x) T.μ := (Lp.memLp a).integrable_mul (Lp.memLp w)
  have hw2 : Integrable (fun x => w x ^ 2) T.μ := (Lp.memLp w).integrable_sq
  have hle : ∫ x, lam * w x ^ 2 ∂T.μ ≤ ∫ x, a x * w x ∂T.μ := by
    refine integral_mono_ae (hw2.const_mul lam) hInt ?_
    filter_upwards [hg, Lp.coeFn_sub g (lam • u), Lp.coeFn_smul lam u,
      Lp.coeFn_sub (clip T lam⁻¹ hc.le u) u, coeFn_clip T lam⁻¹ hc.le u] with x hgx h1 h2 h3 h4
    have e1 : a x = g x - lam * u x := by
      rw [ha, h1, Pi.sub_apply, h2]; simp
    have e2 : w x = min (u x) lam⁻¹ - u x := by
      rw [hw, h3, Pi.sub_apply, h4]
    have hl : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
    simp only [Pi.one_apply] at hgx
    rw [e1, e2]
    rcases le_total (u x) lam⁻¹ with h | h
    · rw [min_eq_left h]; simp
    · rw [min_eq_right h]
      have : lam * u x ≥ lam * lam⁻¹ := by gcongr
      nlinarith [mul_nonneg hlam.le (sq_nonneg (lam⁻¹ - u x))]
  have h0 : ∫ x, lam * w x ^ 2 ∂T.μ ≤ 0 := by linarith
  have h1 : ∫ x, w x ^ 2 ∂T.μ = 0 := by
    rw [integral_const_mul] at h0
    have := integral_nonneg (μ := T.μ) (f := fun x => w x ^ 2) (fun x => sq_nonneg (w x))
    nlinarith
  have h2 := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg (w x)) hw2).1 h1
  filter_upwards [h2, Lp.coeFn_sub (clip T lam⁻¹ hc.le u) u, coeFn_clip T lam⁻¹ hc.le u,
    Lp.coeFn_smul lam (S.resolvent lam g)] with x h3 h4 h5 h6
  have h7 : w x = 0 := by
    have : w x ^ 2 = 0 := h3
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have e2 : w x = min (u x) lam⁻¹ - u x := by
    rw [hw, h4, Pi.sub_apply, h5]
  have hmin : u x ≤ lam⁻¹ := by
    rw [e2] at h7
    have : min (u x) lam⁻¹ = u x := by linarith
    exact min_eq_left_iff.1 this
  show (((lam • S.resolvent lam) g : Lp ℝ 2 T.μ) : E → ℝ) x ≤ 1
  rw [ContinuousLinearMap.smul_apply, h6]
  simp only [Pi.smul_apply, smul_eq_mul]
  have : lam * u x ≤ lam * lam⁻¹ := by gcongr
  rw [mul_inv_cancel₀ hlam.ne'] at this
  exact this

/-- **Second Beurling–Deny criterion: the Friedrichs semigroup of every Markov triple is
sub-Markov**: `u ≤ 1` a.e. implies `P_t u ≤ 1` a.e. -/
theorem tripleSemigroup_subMarkov (t : ℝ≥0) (u : Lp ℝ 2 T.μ)
    (hu : (u : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ)) :
    (tripleSemigroup T t u : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ) :=
  (formData T).semigroup_mapsTo {w : Lp ℝ 2 T.μ | (w : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ)}
    (isClosed_ae_le_one T.μ)
    (fun lam hlam x hx => resolvent_le_one T x hx hlam) t hu

/-- For a bare `MarkovTriple`, the Friedrichs semigroup satisfies `IsSemigroupOf` as soon as it fixes
`1` (only a condition when `μ` is finite; vacuous otherwise). -/
theorem isSemigroupOf_of_conservative
    (hone : ∀ (t : ℝ≥0) (u : Lp ℝ 2 T.μ), (u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ) →
      (tripleSemigroup T t u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ)) :
    MarkovTriple.IsSemigroupOf T (tripleSemigroup T) :=
  isSemigroupOf_of_markov_conservative T (isMarkovianForm T) (tripleSemigroup_subMarkov T) hone

end Clip

end MarkovTriple.Hilbert
