import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctCutoff
import MarkovTriple.BGL.Theory.ESAOne
import MarkovTriple.BGL.Theory.Conservation.Hilbert
import MarkovTriple.BGL.SemigroupLemmas

/-!
# ESA and ergodicity from weak hypo-ellipticity, connexity and completeness (BGL Props. 3.3.10, 3.3.11)

* `WeakHypoElliptic D A` is BGL Def. 3.3.8: every `f ∈ 𝒟(L*)` with `L* f = λ f` lies in `𝒜`
  (`f ∈ 𝒟(L*)`, `L* f = λ f` is spelled out through Def. 3.1.9: `∫ f L a = ∫ λ f a` for all `a ∈ 𝒜₀`).  The book's
  statement quantifies over every `λ ∈ ℝ`; only `λ = 1` (Prop. 3.3.11) and `λ = 0` (Prop. 3.3.10) are used.
* `DiffusionTriple.ESAProp_of_weakHypo` is **BGL Prop. 3.3.11** (connexity + weak hypo-ellipticity +
  completeness ⇒ ESA), following the book's route: the criterion of Prop. A.5.3 (`(1 - L)𝒜₀` dense, i.e.
  `ker(L* - 1) = 0`) and the proof of Prop. 3.2.1 (`FunctCutoff`).
* `DiffusionTriple.ergodic_of_weakHypo` is **BGL Prop. 3.3.10** (connexity + weak hypo-ellipticity ⇒ ergodicity
  S10).  **Status / deviation from the text.**  The book (p. 157) argues: `f ∈ 𝒟(L)`, `L f = 0` ⇒ `f ∈ 𝒜` (weak
  hypo-ellipticity) and, "by integration by parts, `0 = ∫ f L f dμ = -∫ Γ(f) dμ`", hence `Γ(f) = 0` and `f` is
  constant by connexity.  That integration by parts is *not* F7 of the library (F7 is stated for `g ∈ 𝒜₀`,
  Def. 3.3.1 (vii)); for `f ∈ 𝒟(L) ∩ 𝒜` it would need the identification of the Friedrichs form with `∫ Γ`
  on `𝒟(ℰ) ∩ 𝒜`, which is not available.  Here the step `Γ(f) = 0` is instead obtained from the
  integration-by-parts computation *of the proof of Prop. 3.2.1* (`PreFull.gradient_eq_zero`: test `L f = 0`
  against `f ζ_k²`, F7 with `f ζ_k² ∈ 𝒜₀`, and let `k → ∞`), which the book itself says "immediately extends"
  to the abstract setting (paragraph following Prop. 3.3.10).  It therefore uses completeness
  (Def. 3.3.9) in addition to the hypotheses listed in the statement of Prop. 3.3.10; everything else follows the
  book.  This is the only place where the formalisation differs from the text of Prop. 3.3.10.
* In `PreFull.cutoff_estimate` the integral Cauchy-Schwarz step of the proof of Prop. 3.2.1 is carried out as the
  equivalent pointwise inequality `2|fζ||Γ(ζ,f)| ≤ ½ζ²Γ(f) + 2ε²f²` (constants `4ε²‖f‖₂²` as in the book).
-/

open MeasureTheory Filter Topology
open scoped NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- **Weak hypo-ellipticity** (BGL Def. 3.3.8): for every `λ ∈ ℝ`, any `f ∈ L²` which belongs to `𝒟(L*)` with
`L* f = λ f` (i.e. `∫ f L a = λ ∫ f a` for every `a ∈ 𝒜₀`, Def. 3.1.9) has a representative in `𝒜`. -/
def DiffusionTriple.WeakHypoElliptic (D : DiffusionTriple E) (A : Subalgebra ℝ (E → ℝ)) : Prop :=
  ∀ (l : ℝ) (f : Lp ℝ 2 D.μ),
    (∀ a : D.A₀, ∫ x, (f : E → ℝ) x * D.L a.1 x ∂D.μ = ∫ x, (l * (f : E → ℝ) x) * a.1 x ∂D.μ) →
      ∃ g ∈ A, (f : E → ℝ) =ᵐ[D.μ] g

namespace PreFull

variable {D : DiffusionTriple E} {A : Subalgebra ℝ (E → ℝ)} (h : PreFull D A)
include h

/-- A representative `g ∈ 𝒜` of a weak solution of `L* f = λ f` satisfies `L g = λ g` a.e. -/
theorem L_eq_of_weak {l : ℝ} {f : Lp ℝ 2 D.μ} {g : E → ℝ} (hg : g ∈ A) (hfg : (f : E → ℝ) =ᵐ[D.μ] g)
    (hweak : ∀ a : D.A₀, ∫ x, (f : E → ℝ) x * D.L a.1 x ∂D.μ = ∫ x, (l * (f : E → ℝ) x) * a.1 x ∂D.μ) :
    D.L g =ᵐ[D.μ] fun x => l * g x := by
  set f₁ : E → ℝ := D.L g - l • g with hf₁
  have hf₁A : f₁ ∈ A := A.sub_mem (h.L_mem_A g hg) (A.smul_mem hg l)
  have hint : ∀ a ∈ D.A₀, ∫ x, a x * f₁ x ∂D.μ = 0 := by
    intro a ha
    have i1 : Integrable (fun x => a x * D.L g x) D.μ :=
      DiffusionTriple.integrable_of_mem D (h.ideal _ (h.L_mem_A g hg) a ha)
    have i2 : Integrable (fun x => a x * g x) D.μ :=
      DiffusionTriple.integrable_of_mem D (h.ideal _ hg a ha)
    have s1 := (h.ibp_A g hg a ha).1
    have s2 := (h.ibp_A g hg a ha).2
    have w1 := hweak ⟨a, ha⟩
    have e1 : ∫ x, (f : E → ℝ) x * D.L a x ∂D.μ = ∫ x, g x * D.L a x ∂D.μ :=
      integral_congr_ae (by filter_upwards [hfg] with x hx; rw [hx])
    have e2 : ∫ x, (l * (f : E → ℝ) x) * a x ∂D.μ = l * ∫ x, a x * g x ∂D.μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (by filter_upwards [hfg] with x hx; simp only [hx]; ring)
    have e3 : ∫ x, a x * f₁ x ∂D.μ = ∫ x, a x * D.L g x ∂D.μ - l * ∫ x, a x * g x ∂D.μ := by
      rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul l)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [hf₁, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
    rw [e3]
    rw [e1, e2] at w1
    linarith
  have p1 : 0 ≤ᵐ[D.μ] f₁ := h.pos_detect f₁ hf₁A (fun a ha _ => (hint a ha).ge)
  have p2 : 0 ≤ᵐ[D.μ] -f₁ := h.pos_detect (-f₁) (A.neg_mem hf₁A) (fun a ha _ => by
    have : ∫ x, a x * (-f₁) x ∂D.μ = 0 := by
      simp only [Pi.neg_apply, mul_neg, integral_neg, hint a ha, neg_zero]
    exact this.ge)
  filter_upwards [p1, p2] with x a b
  simp only [Pi.neg_apply, Pi.zero_apply] at a b
  have : f₁ x = 0 := le_antisymm (by linarith) a
  simp only [hf₁, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-- If a weak solution of `L* f = λ f` (`λ ≥ 0`) lies in `𝒜` it has `Γ(g) = 0`, hence is a.e. constant
(complete + connected triple). -/
theorem const_of_weak (hC : D.IsComplete) {l : ℝ} (hl : 0 ≤ l) {f : Lp ℝ 2 D.μ} {g : E → ℝ}
    (hg : g ∈ A) (hfg : (f : E → ℝ) =ᵐ[D.μ] g)
    (hweak : ∀ a : D.A₀, ∫ x, (f : E → ℝ) x * D.L a.1 x ∂D.μ = ∫ x, (l * (f : E → ℝ) x) * a.1 x ∂D.μ) :
    ∃ c : ℝ, (f : E → ℝ) =ᵐ[D.μ] fun _ => c := by
  have hL := h.L_eq_of_weak hg hfg hweak
  have hg2 : MemLp g 2 D.μ := (Lp.memLp f).ae_eq hfg
  have hsign : ∀ᵐ x ∂D.μ, 0 ≤ g x * D.L g x := by
    filter_upwards [hL] with x hx
    rw [hx]
    have : g x * (l * g x) = l * (g x * g x) := by ring
    rw [this]; exact mul_nonneg hl (mul_self_nonneg _)
  have h0 := h.gradient_eq_zero hC hg hg2 hsign
  obtain ⟨c, hc⟩ := h.connected g hg h0
  exact ⟨c, hfg.trans hc⟩

end PreFull

namespace DiffusionTriple

variable (T : DiffusionTriple E)

/-- **Core of the Friedrichs generator from density of `(1 - L)𝒜₀`** (BGL Prop. A.5.3 / Def. 3.1.10).  The
tail of `core_of_invariant`. -/
theorem core_of_orth
    (horth : ∀ w : Lp ℝ 2 T.μ, (∀ a : T.A₀, inner ℝ (T.cls a - T.Lcls a) w = 0) → w = 0) :
    T.ESAProp := by
  intro u hu
  set S := formData T with hS
  let M : Submodule ℝ (Lp ℝ 2 T.μ) := (LinearMap.range (clsₗ T - Lclsₗ T))
  have hM : M.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    exact horth w (fun a => hw _ ⟨a, rfl⟩)
  have hdense : Dense (M : Set (Lp ℝ 2 T.μ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 hM
  set g : Lp ℝ 2 T.μ := u - S.generator ⟨u, hu⟩ with hg
  obtain ⟨m, hmM, hmg⟩ := mem_closure_iff_seq_limit.1 (hdense.closure_eq ▸ Set.mem_univ g)
  have hm : ∀ n, ∃ a : T.A₀, T.cls a - T.Lcls a = m n := by
    intro n
    obtain ⟨a, ha⟩ := hmM n
    exact ⟨a, ha⟩
  choose a ha using hm
  have hRu : S.R g = u := (S.generator_apply_eq_iff hu _).1 rfl
  have h1 : Tendsto (fun n => T.cls (a n)) atTop (𝓝 u) := by
    have : Tendsto (fun n => S.R (m n)) atTop (𝓝 (S.R g)) := (S.R.continuous.tendsto g).comp hmg
    rw [hRu] at this
    refine this.congr (fun n => ?_)
    rw [← ha n]; exact R_cls_sub T (a n)
  refine ⟨a, h1, ?_⟩
  have h2 : Tendsto (fun n => T.cls (a n) - m n) atTop (𝓝 (u - g)) := h1.sub hmg
  have e : u - g = S.generator ⟨u, hu⟩ := by rw [hg]; abel
  rw [e] at h2
  refine h2.congr (fun n => ?_)
  rw [← ha n]; abel

/-- **BGL Prop. 3.3.11**: connexity + weak hypo-ellipticity + completeness ⇒ ESA (F10, core form). -/
theorem ESAProp_of_weakHypo {A : Subalgebra ℝ (E → ℝ)} (h : PreFull T A) (hC : T.IsComplete)
    (hH : T.WeakHypoElliptic A) : T.ESAProp := by
  refine core_of_orth T (fun w hw => ?_)
  have hweak : ∀ a : T.A₀, ∫ x, (w : E → ℝ) x * T.L a.1 x ∂T.μ =
      ∫ x, (1 * (w : E → ℝ) x) * a.1 x ∂T.μ := by
    intro a
    have := hw a
    rw [inner_sub_left, sub_eq_zero, L2_inner_eq, L2_inner_eq] at this
    have e1 : ∫ x, (T.cls a : E → ℝ) x * (w : E → ℝ) x ∂T.μ = ∫ x, (w : E → ℝ) x * a.1 x ∂T.μ :=
      integral_congr_ae (by filter_upwards [coeFn_cls T a] with x hx; rw [hx]; ring)
    have e2 : ∫ x, (T.Lcls a : E → ℝ) x * (w : E → ℝ) x ∂T.μ =
        ∫ x, (w : E → ℝ) x * T.L a.1 x ∂T.μ :=
      integral_congr_ae (by filter_upwards [coeFn_Lcls T a] with x hx; rw [hx]; ring)
    rw [e1, e2] at this
    simp only [one_mul]
    exact this.symm
  obtain ⟨g, hgA, hwg⟩ := hH 1 w hweak
  obtain ⟨c, hc⟩ := h.const_of_weak hC zero_le_one hgA hwg hweak
  -- `w = c`, and `c ∫ a = ⟪a, w⟫ = ⟪L a, w⟫ = c ∫ L a = 0`
  refine T.eq_zero_of_orth w (fun a => ?_)
  rw [real_inner_comm, L2_inner_eq]
  have e1 : ∫ x, (T.cls a : E → ℝ) x * (w : E → ℝ) x ∂T.μ = c * ∫ x, a.1 x ∂T.μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (by filter_upwards [coeFn_cls T a, hc] with x h1 h2; rw [h1, h2]; ring)
  have e2 : ∫ x, (T.Lcls a : E → ℝ) x * (w : E → ℝ) x ∂T.μ = c * ∫ x, T.L a.1 x ∂T.μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (by
      filter_upwards [coeFn_Lcls T a, hc] with x h1 h2; rw [h1, h2]; ring)
  have h0 := hw a
  rw [inner_sub_left, sub_eq_zero, L2_inner_eq, L2_inner_eq, e1, e2, T.integral_L a.1 a.2] at h0
  rw [e1]
  simpa using h0

/-- **BGL Prop. 3.3.10** (see the module docstring for the cut-off justification): connexity + weak
hypo-ellipticity (+ completeness) ⇒ ergodicity (S10). -/
theorem ergodic_of_weakHypo {A : Subalgebra ℝ (E → ℝ)} (h : PreFull T A) (hC : T.IsComplete)
    (hH : T.WeakHypoElliptic A) :
    ∀ (u : Lp ℝ 2 T.μ) (hu : u ∈ T.generator.domain), T.generator ⟨u, hu⟩ = 0 →
      ∃ c : ℝ, (u : E → ℝ) =ᵐ[T.μ] fun _ => c := by
  intro u hu hGu
  have hweak : ∀ a : T.A₀, ∫ x, (u : E → ℝ) x * T.L a.1 x ∂T.μ =
      ∫ x, (0 * (u : E → ℝ) x) * a.1 x ∂T.μ := by
    intro a
    have hs := Hilbert.FormData.generator_symm (formData T) hu (cls_mem_generator_domain T a)
    have hGa := generator_cls T a (cls_mem_generator_domain T a)
    change inner ℝ (T.generator ⟨u, hu⟩) (T.cls a) =
      inner ℝ u (T.generator ⟨T.cls a, cls_mem_generator_domain T a⟩) at hs
    rw [hGa, hGu, inner_zero_left, L2_inner_eq] at hs
    simp only [zero_mul, integral_zero]
    rw [hs]
    exact (integral_congr_ae (by filter_upwards [coeFn_Lcls T a] with x hx; rw [hx])).symm
  obtain ⟨g, hgA, hug⟩ := hH 0 u hweak
  exact h.const_of_weak hC le_rfl hgA hug hweak

end DiffusionTriple

end MarkovTriple.BGL
