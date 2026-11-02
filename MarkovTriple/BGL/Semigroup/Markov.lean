import Mathlib
import MarkovTriple.BGL.Frozen.Semigroup
import MarkovTriple.BGL.Frozen.FormDomain
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Calculus.Identities
import MarkovTriple.BGL.Analysis.Hilbert.Truncation
import MarkovTriple.BGL.Analysis.Hilbert.Contraction

/-!
# Positivity and sub-Markov property of the semigroup of a `DiffusionTriple` (BGL §3.1.5–3.1.6)

Port of `Hilbert/BeurlingDeny.lean`, `Hilbert/MarkovCriterion.lean`, `Hilbert/SubMarkov.lean` from the
old `MarkovTriple` to the new `DiffusionTriple` (a.e. fields).  Only the abstract Friedrichs
statements (`Hilbert.FormData.*`) and the pure real-analysis lemmas on `√(t²+δ²)` are re-used.

* `DiffusionTriple.isMarkovianForm` (first Beurling–Deny): `u ∈ 𝒟(ℰ) ⇒ |u| ∈ 𝒟(ℰ)`, `ℰ(|u|) ≤ ℰ(u)`.
  `𝒜₀` is stable under `ψ_δ(t) = √(t²+δ²) − δ` (`ψ_δ(0) = 0`, `comp_mem`), `Γ(ψ_δ f) = ψ_δ'(f)² Γ(f) ≤ Γ(f)`
  by the diffusion property, and `ψ_δ(f) → |f|` in `L²`.
* `DiffusionTriple.semigroup_nonneg`: `P_t` is positivity preserving.
* `DiffusionTriple.isClipForm` (second Beurling–Deny): `u ∧ c` is a normal contraction of the form,
  via the smooth truncations `ψ_δ(t) = (t − √((t−c)²+δ²) + √(c²+δ²))/2`.
* `DiffusionTriple.semigroup_le_one`: `u ≤ 1` a.e. `⇒ P_t u ≤ 1` a.e. (sub-Markov).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace LinearPMap

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-! ### Generic `L²(μ)` lemmas -/

section Generic

variable {μ : Measure E}

lemma norm_abs_eq' (u : Lp ℝ 2 μ) : ‖|u|‖ = ‖u‖ := by
  have h : inner ℝ |u| |u| = inner ℝ u u := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_abs u] with x hx
    rw [hx]
    simp
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg |u|, norm_nonneg u, sq_nonneg (‖|u|‖ - ‖u‖), sq_nonneg (‖|u|‖ + ‖u‖)]

lemma inner_nonneg_of_ae' {g w : Lp ℝ 2 μ} (hg : 0 ≤ᵐ[μ] g) (hw : 0 ≤ᵐ[μ] w) :
    0 ≤ inner ℝ g w := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hg, hw] with x h1 h2
  simp only [Pi.zero_apply] at h1 h2
  simpa [mul_comm] using mul_nonneg h1 h2

lemma lipschitz_abs' (u v : Lp ℝ 2 μ) : ‖|u| - |v|‖ ≤ 1 * ‖u - v‖ := by
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub |u| |v|, Lp.coeFn_abs u, Lp.coeFn_abs v, Lp.coeFn_sub u v]
    with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_abs_sub_abs_le_abs_sub _ _

lemma exists_small_min' (f : E → ℝ) (hf : MemLp f 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∫ x, (min δ |f x|) ^ 2 ∂μ < ε := by
  have hint : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ x, (min (1 / ((n:ℝ)+1)) |f x|) ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => f x ^ 2)
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
          refine squeeze_zero (fun n => le_min (by positivity) (abs_nonneg _))
            (fun n => min_le_left _ _) tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using h.pow 2)
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨1 / ((n:ℝ)+1), by positivity, hn⟩

lemma integrable_min_sq' (f : E → ℝ) (hf : MemLp f 2 μ) (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun x => (min δ |f x|) ^ 2) μ := by
  refine hf.integrable_sq.mono'
    ((aemeasurable_const.min hf.aemeasurable.norm).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ min δ |f x| := le_min hδ.le (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc _ ≤ |f x| ^ 2 := by gcongr; exact min_le_right _ _
    _ = f x ^ 2 := sq_abs _

lemma memLp_clip' (c : ℝ) (hc : 0 ≤ c) (u : Lp ℝ 2 μ) :
    MemLp (fun x => min (u x) c) 2 μ := by
  refine (Lp.memLp u).of_le
    (((Lp.aestronglyMeasurable u).aemeasurable.min aemeasurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs] using Hilbert.abs_min_le (u x) c hc

/-- The clip `u ↦ u ∧ c` on `L²(μ)` (`c ≥ 0`). -/
noncomputable def clip' (c : ℝ) (hc : 0 ≤ c) (u : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (memLp_clip' c hc u).toLp _

lemma coeFn_clip' (c : ℝ) (hc : 0 ≤ c) (u : Lp ℝ 2 μ) :
    (clip' c hc u : E → ℝ) =ᵐ[μ] fun x => min (u x) c :=
  MemLp.coeFn_toLp _

lemma lipschitz_clip' (c : ℝ) (hc : 0 ≤ c) (u v : Lp ℝ 2 μ) :
    ‖clip' c hc u - clip' c hc v‖ ≤ 1 * ‖u - v‖ := by
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (clip' c hc u) (clip' c hc v), coeFn_clip' c hc u,
    coeFn_clip' c hc v, Lp.coeFn_sub u v] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  have := abs_min_sub_min_le_max (u x) c (v x) c
  simpa using this

end Generic

/-! ### The Markov property of the form -/

namespace DiffusionTriple

variable (T : DiffusionTriple E)

/-! #### `L²` semigroup properties (restated for the new surface) -/

theorem semigroup_zero : T.semigroup 0 = 1 := (formData T).semigroup_zero

theorem semigroup_add (s t : ℝ≥0) : T.semigroup (s + t) = T.semigroup s * T.semigroup t :=
  (formData T).semigroup_add s t

/-- `L²`-contractivity. -/
theorem norm_semigroup_le (t : ℝ≥0) : ‖T.semigroup t‖ ≤ 1 := (formData T).norm_semigroup_le t

theorem norm_semigroup_apply_le (t : ℝ≥0) (u : Lp ℝ 2 T.μ) : ‖T.semigroup t u‖ ≤ ‖u‖ :=
  (T.semigroup t).le_opNorm u |>.trans (by
    simpa using mul_le_mul_of_nonneg_right (T.norm_semigroup_le t) (norm_nonneg u))

theorem semigroup_isSelfAdjoint (t : ℝ≥0) : IsSelfAdjoint (T.semigroup t) :=
  (formData T).semigroup_isSelfAdjoint t

theorem continuous_semigroup_apply (u : Lp ℝ 2 T.μ) : Continuous fun t : ℝ≥0 => T.semigroup t u :=
  (formData T).continuous_semigroup_apply u

lemma en_eq_qf (f g : T.A₀) :
    (formData T).en ⟨clsₗ T f, ⟨f, rfl⟩⟩ ⟨clsₗ T g, ⟨g, rfl⟩⟩ = qf T f g :=
  inner_formA T f g

/-- Composition with a smooth `ψ`, `ψ(0)=0`, `|ψ'| ≤ 1` stays in `𝒜₀` and does not increase the
energy (diffusion property). -/
lemma comp_qf_le {ψ : (Fin 1 → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (hb : ∀ z, |pderiv ψ 0 z| ≤ 1) (f : T.A₀) :
    ∃ hg : (fun x => ψ (fun _ => f.1 x)) ∈ T.A₀,
      qf T ⟨_, hg⟩ ⟨_, hg⟩ ≤ qf T f f := by
  set g : E → ℝ := fun x => ψ (fun _ => f.1 x) with hg
  have hgmem : g ∈ T.A₀ := T.comp_mem 1 ψ hψ h0 (fun _ => f.1) (fun _ => f.2)
  refine ⟨hgmem, ?_⟩
  have hd := T.diffusion 1 ψ hψ h0 (fun _ => f.1) (fun _ => f.2) g hgmem
  have hd2 := T.diffusion 1 ψ hψ h0 (fun _ => f.1) (fun _ => f.2) f.1 f.2
  have key : ∀ᵐ x ∂T.μ, T.Γ g g x = (pderiv ψ 0 (fun _ => f.1 x)) ^ 2 * T.Γ f.1 f.1 x := by
    filter_upwards [hd, hd2, T.Γ_symm f.1 f.2 g hgmem] with x h1 h2 h3
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at h1 h2
    rw [h1, h3, h2]; ring
  have hmono : ∫ x, T.Γ g g x ∂T.μ ≤ ∫ x, T.Γ f.1 f.1 x ∂T.μ := by
    refine integral_mono_ae (Γ_integrable T ⟨g, hgmem⟩ ⟨g, hgmem⟩) (Γ_integrable T f f) ?_
    filter_upwards [key, T.Γ_nonneg f.1 f.2] with x hk hn
    rw [hk]
    have hp : (pderiv ψ 0 (fun _ => f.1 x)) ^ 2 ≤ 1 := by
      have := hb (fun _ => f.1 x)
      nlinarith [sq_abs (pderiv ψ 0 (fun _ => f.1 x)), abs_nonneg (pderiv ψ 0 (fun _ => f.1 x))]
    simp only [Pi.zero_apply] at hn
    nlinarith
  exact hmono

/-- **First Beurling–Deny criterion** (Markov property of the closed form): for `u ∈ 𝒟(ℰ)`,
`|u| ∈ 𝒟(ℰ)` and `ℰ(|u|) ≤ ℰ(u)`. -/
theorem isMarkovianForm : ∀ u : (formData T).Q, ∃ v : (formData T).Q,
    (v : Lp ℝ 2 T.μ) = |(u : Lp ℝ 2 T.μ)| ∧ (formData T).E v v ≤ (formData T).E u u := by
  intro u
  refine (formData T).exists_contraction_of_approx (fun w => |w|) 1 lipschitz_abs' ?_ u
  intro f ε hε
  obtain ⟨_, f', rfl⟩ := f
  obtain ⟨δ, hδ, hint⟩ := exists_small_min' f'.1 (memLp2 T f'.2) (pow_pos hε 2)
  have hb : ∀ z, |pderiv (Hilbert.trunc δ) 0 z| ≤ 1 := fun z => Hilbert.abs_pderiv_trunc_le hδ z
  obtain ⟨hgmem, hq⟩ := comp_qf_le T (Hilbert.contDiff_trunc hδ) (Hilbert.trunc_zero hδ) hb f'
  set g : E → ℝ := fun x => Hilbert.trunc δ (fun _ => f'.1 x) with hg
  refine ⟨⟨clsₗ T ⟨g, hgmem⟩, ⟨⟨g, hgmem⟩, rfl⟩⟩, ?_, ?_⟩
  · set v : Lp ℝ 2 T.μ := clsₗ T ⟨g, hgmem⟩ - |clsₗ T f'| with hv
    have e : ‖v‖ ^ 2 = ∫ x, (g x - |f'.1 x|) ^ 2 ∂T.μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (clsₗ T ⟨g, hgmem⟩) |clsₗ T f'|,
        coeFn_cls T ⟨g, hgmem⟩, coeFn_cls T f', Lp.coeFn_abs (clsₗ T f')] with x h1 h2 h3 h4
      rw [hv, h1, Pi.sub_apply, h4]
      have h2' : (clsₗ T ⟨g, hgmem⟩ : E → ℝ) x = g x := h2
      have h3' : (clsₗ T f' : E → ℝ) x = f'.1 x := h3
      rw [h2', h3']
      simp [sq]
    have hle : ∫ x, (g x - |f'.1 x|) ^ 2 ∂T.μ ≤ ∫ x, (min δ |f'.1 x|) ^ 2 ∂T.μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        (integrable_min_sq' f'.1 (memLp2 T f'.2) δ hδ) (Filter.Eventually.of_forall fun x => ?_)
      obtain ⟨h0, h1⟩ := Hilbert.trunc_bounds hδ (f'.1 x)
      have : g x - |f'.1 x| = -(|f'.1 x| - (√(f'.1 x ^ 2 + δ ^ 2) - δ)) := by
        simp only [hg, Hilbert.trunc]; ring
      show (g x - |f'.1 x|) ^ 2 ≤ (min δ |f'.1 x|) ^ 2
      rw [this, neg_sq]
      exact pow_le_pow_left₀ h0 h1 2
    have : ‖v‖ ^ 2 < ε ^ 2 := by rw [e]; exact lt_of_le_of_lt hle hint
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  · rw [en_eq_qf T ⟨g, hgmem⟩ ⟨g, hgmem⟩, en_eq_qf T f' f']
    linarith

/-- **Positivity preservation**: `u ≥ 0` a.e. `⇒ P_t u ≥ 0` a.e. -/
theorem semigroup_nonneg (t : ℝ≥0) {u : Lp ℝ 2 T.μ} (hu : 0 ≤ᵐ[T.μ] u) :
    0 ≤ᵐ[T.μ] T.semigroup t u := by
  have hC : IsClosed {w : Lp ℝ 2 T.μ | 0 ≤ᵐ[T.μ] w} := by
    have : {w : Lp ℝ 2 T.μ | 0 ≤ᵐ[T.μ] w} = Set.Ici 0 := by
      ext w; exact Lp.coeFn_nonneg w
    rw [this]; exact isClosed_Ici
  exact (formData T).semigroup_mapsTo_of_contraction (fun w => |w|)
    {w : Lp ℝ 2 T.μ | 0 ≤ᵐ[T.μ] w} hC
    (fun c hc x hx => by
      have hx' : 0 ≤ᵐ[T.μ] x := hx
      show 0 ≤ᵐ[T.μ] c • x
      filter_upwards [Lp.coeFn_smul c x, hx'] with a h1 h2
      simp only [Pi.zero_apply] at h2 ⊢
      rw [h1]; simpa using mul_nonneg hc h2)
    (fun u => isMarkovianForm T u)
    (fun u => (norm_abs_eq' u).le)
    (fun g hg w => by
      have hg' : 0 ≤ᵐ[T.μ] g := hg
      apply inner_nonneg_of_ae' hg'
      filter_upwards [Lp.coeFn_sub |w| w, Lp.coeFn_abs w] with a h1 h2
      rw [h1, Pi.sub_apply, h2]
      simp only [Pi.zero_apply, sub_nonneg]
      exact le_abs_self _)
    (fun w hw => by
      have hw' : (|w| : Lp ℝ 2 T.μ) = w := hw
      show 0 ≤ᵐ[T.μ] w
      filter_upwards [Lp.coeFn_abs w,
        Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 T.μ => (z : E → ℝ)) hw')]
        with a h1 h2
      simp only [Pi.zero_apply]
      rw [← h2, h1]
      exact abs_nonneg _) t hu

/-! ### Second Beurling–Deny: sub-Markov -/

/-- **The clip `u ↦ u ∧ c` is a normal contraction for the closed form**: for every `u ∈ 𝒟(ℰ)`,
`u ∧ c ∈ 𝒟(ℰ)` and `ℰ(u ∧ c) ≤ ℰ(u)` (`c > 0`). -/
theorem isClipForm {c : ℝ} (hc : 0 < c) : ∀ u : (formData T).Q, ∃ v : (formData T).Q,
    (v : Lp ℝ 2 T.μ) = clip' c hc.le (u : Lp ℝ 2 T.μ) ∧ (formData T).E v v ≤ (formData T).E u u := by
  intro u
  refine (formData T).exists_contraction_of_approx (clip' c hc.le) 1
    (lipschitz_clip' c hc.le) ?_ u
  intro f ε hε
  obtain ⟨_, f', rfl⟩ := f
  obtain ⟨δ, hδ, hint⟩ := exists_small_min' f'.1 (memLp2 T f'.2) (pow_pos (half_pos hε) 2)
  obtain ⟨hg, hq⟩ := comp_qf_le T (Hilbert.contDiff_clipFn hδ c) (Hilbert.clipFn_zero c δ)
    (fun z => Hilbert.abs_pderiv_clipFn_le hδ c z) f'
  set g : E → ℝ := fun x => Hilbert.clipFn c δ (fun _ => f'.1 x) with hgdef
  refine ⟨⟨clsₗ T ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩, ?_, ?_⟩
  · have e : ‖clsₗ T ⟨g, hg⟩ - clip' c hc.le (clsₗ T f')‖ ^ 2 =
        ∫ x, (g x - min (f'.1 x) c) ^ 2 ∂T.μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (clsₗ T ⟨g, hg⟩) (clip' c hc.le (clsₗ T f')),
        coeFn_cls T ⟨g, hg⟩, coeFn_clip' c hc.le (clsₗ T f'), coeFn_cls T f']
        with x h1 h2 h3 h4
      have h2' : (clsₗ T ⟨g, hg⟩ : E → ℝ) x = g x := h2
      have h4' : (clsₗ T f' : E → ℝ) x = f'.1 x := h4
      rw [h1, Pi.sub_apply, h2', h3, h4']
      simp [sq]
    have hle : ∫ x, (g x - min (f'.1 x) c) ^ 2 ∂T.μ ≤
        ∫ x, 4 * (min δ |f'.1 x|) ^ 2 ∂T.μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        ((integrable_min_sq' f'.1 (memLp2 T f'.2) δ hδ).const_mul 4)
        (Filter.Eventually.of_forall fun x => ?_)
      obtain ⟨b1, b2⟩ := Hilbert.clipFn_bounds hδ hc.le (f'.1 x)
      have b3 := Hilbert.abs_min_le (f'.1 x) c hc.le
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
    have : ‖clsₗ T ⟨g, hg⟩ - clip' c hc.le (clsₗ T f')‖ ^ 2 < ε ^ 2 := by
      rw [e]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  · rw [en_eq_qf T ⟨g, hg⟩ ⟨g, hg⟩, en_eq_qf T f' f']
    linarith

/-- **Resolvent estimate**: `g ≤ 1` a.e. implies `λ R_λ g ≤ 1` a.e. -/
theorem resolvent_le_one (g : Lp ℝ 2 T.μ) (hg : (g : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ))
    {lam : ℝ} (hlam : 0 < lam) :
    (((lam • (formData T).resolvent lam) g : Lp ℝ 2 T.μ) : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ) := by
  set S := formData T with hS
  set u : Lp ℝ 2 T.μ := S.resolvent lam g with hu
  have hc : 0 < lam⁻¹ := inv_pos.2 hlam
  set a : Lp ℝ 2 T.μ := g - lam • u with ha
  set w : Lp ℝ 2 T.μ := clip' lam⁻¹ hc.le u - u with hw
  have hpair := S.resolvent_pairing_nonpos (clip' lam⁻¹ hc.le)
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
      Lp.coeFn_sub (clip' lam⁻¹ hc.le u) u, coeFn_clip' lam⁻¹ hc.le u]
      with x hgx h1 h2 h3 h4
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
  have h2 := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => sq_nonneg (w x)) hw2).1 h1
  filter_upwards [h2, Lp.coeFn_sub (clip' lam⁻¹ hc.le u) u, coeFn_clip' lam⁻¹ hc.le u,
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

/-- **Sub-Markov property** (second Beurling–Deny criterion): `u ≤ 1` a.e. `⇒ P_t u ≤ 1` a.e. -/
theorem semigroup_le_one (t : ℝ≥0) (u : Lp ℝ 2 T.μ) (hu : (u : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ)) :
    (T.semigroup t u : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ) :=
  (formData T).semigroup_mapsTo {w : Lp ℝ 2 T.μ | (w : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ)}
    (Hilbert.isClosed_ae_le_one T.μ)
    (fun lam hlam x hx => resolvent_le_one T x hx hlam) t hu

end DiffusionTriple

end MarkovTriple.BGL
