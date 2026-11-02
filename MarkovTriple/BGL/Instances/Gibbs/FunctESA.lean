import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctCutoff
import MarkovTriple.BGL.Theory.ESAOne
import MarkovTriple.BGL.Theory.Conservation.Hilbert

/-!
# Gibbs measures: ESA (F10) and ergodicity (S10) by the book's route

BGL, Prop. 3.2.1 / Cor. 3.2.2 / Props. 3.3.10–3.3.11: for a complete, connected, weakly hypo-elliptic
Diffusion Markov Triple, `L` is essentially self-adjoint on `𝒜₀` and ergodic.

For the Gibbs triple `gibbsDiff` (`𝒜₀ = C_c^∞`, `𝒜 = C^∞`) we have:
* completeness (`gibbsDiff_isComplete`, already proved);
* connexity (F9) is the elementary fact "`f' = 0` ⇒ `f` constant" (used inside `cutoff_conclusion`);
* weak hypo-ellipticity (BGL Def. 3.3.8): every `f ∈ 𝒟(L*)` with `L* f = λ f` is in `𝒜`.
  This is the one input that the book does not prove (it is elliptic regularity for `f'' - V' f' = λ f`,
  "hypo-ellipticity, Sect. 1.12"); here it is the explicit hypothesis `WeakHypoEllipticAt λ`
  (for `λ = 1` and `λ = 0` only).

Proved here, **conditionally on `WeakHypoEllipticAt 1` (resp. `0`)**:
* `gibbsDiff_esaProp`  (F10 in the frozen core form, Prop. 3.2.1);
* `gibbsDiff_ergodic`  (S10, Prop. 3.3.10).
-/

open MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace LinearPMap
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace DiffusionTriple

variable (T : DiffusionTriple E)

lemma inner_cls_eq (a : T.A₀) (w : Lp ℝ 2 T.μ) :
    inner ℝ (T.cls a) w = ∫ x, w x * a.1 x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cls T a] with x hx
  rw [hx, mul_comm]

lemma inner_Lcls_eq (a : T.A₀) (w : Lp ℝ 2 T.μ) :
    inner ℝ (T.Lcls a) w = ∫ x, w x * T.L a.1 x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_Lcls T a] with x hx
  rw [hx, mul_comm]

/-- **ESA from the range criterion** (the resolvent form of BGL Prop. A.5.3 used for Prop. 3.2.1):
if the only `w ∈ L²` orthogonal to `(1 - L)𝒜₀` is `0`, then `𝒜₀` is a core for the Friedrichs generator. -/
theorem esaProp_of_orth
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
  have hdense : Dense (M : Set (Lp ℝ 2 T.μ)) := by
    exact Submodule.dense_iff_topologicalClosure_eq_top.2 hM
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

end DiffusionTriple

end MarkovTriple.BGL

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- **Weak hypo-ellipticity at `λ`** (BGL Def. 3.3.8, for the Gibbs triple, `𝒜 = C^∞(ℝ)`): every
`u ∈ L²(μ)` with `L* u = λ u` (`∫ u L a dμ = λ ∫ u a dμ` for all `a ∈ 𝒜₀`, BGL Def. 3.1.9) has a smooth
representative.  This is elliptic regularity for `u'' - V' u' = λ u`; BGL takes it as the
hypo-ellipticity input (Sect. 1.12, Prop. 3.2.1) and does not prove it. -/
def WeakHypoEllipticAt (lam : ℝ) : Prop :=
  ∀ u : Lp ℝ 2 G.μ,
    (∀ a ∈ OA₀, ∫ x, u x * Lg G.V a x ∂G.μ = lam * ∫ x, u x * a x ∂G.μ) →
      ∃ f : ℝ → ℝ, Sm f ∧ (u : ℝ → ℝ) =ᵐ[G.μ] f

/-- The cut-off computation of BGL Prop. 3.2.1: a smooth `L²` solution of `L f = λ f` with
`λ = 1` vanishes, and with `λ = 0` is constant. -/
lemma cutoff_conclusion {f : ℝ → ℝ} (hf : Sm f) (hfL2 : MemLp f 2 G.μ) (lam : ℝ)
    (hL : ∀ x, Lg G.V f x = lam * f x) :
    (lam = 1 → f =ᵐ[G.μ] 0) ∧ (lam = 0 → ∀ x, deriv f x = 0) := by
  obtain ⟨ζ, hζA, -, -, hζlim, hζΓ⟩ := G.gibbsDiff_isComplete
  have hζA' : ∀ k, ζ k ∈ OA₀ := hζA
  have hζε : ∀ k, ∀ᵐ x ∂G.μ, deriv (ζ k) x * deriv (ζ k) x ≤ (1 / ((k : ℝ) + 1)) ^ 2 :=
    fun k => (hζΓ k).mono fun x hx => hx
  have hineq := fun k : ℕ => cutoff_ineq G hf hfL2 (hζA' k) lam (1 / ((k : ℝ) + 1))
    (by positivity) (hζε k) hL
  set N : ℝ := ∫ x, f x ^ 2 ∂G.μ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun x => sq_nonneg _
  have hζm : ∀ k, Measurable (ζ k) := fun k => (hζA' k).1.continuous.measurable
  have hint : ∀ (h : ℝ → ℝ), Continuous h → ∀ k, Integrable (fun x => h x * (ζ k x * ζ k x)) G.μ :=
    fun h hh k => (hh.mul ((hζA' k).1.continuous.mul (hζA' k).1.continuous)).integrable_of_hasCompactSupport
      ((hζA' k).2.mul_right.mul_left)
  have hεt : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hB0 : ∀ k : ℕ, 0 ≤ ∫ x, deriv f x ^ 2 * (ζ k x * ζ k x) ∂G.μ := fun k =>
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
  constructor
  · intro h1
    subst h1
    have hA : ∀ k : ℕ, ∫ x, f x ^ 2 * (ζ k x * ζ k x) ∂G.μ ≤ (1 / ((k : ℝ) + 1)) * N := by
      intro k
      have := hineq k
      have hε1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hB := hB0 k
      nlinarith [mul_nonneg (sub_nonneg.2 hε1) hB]
    have hz := zero_of_cutoff (μ := G.μ) (h := fun x => f x ^ 2) (hf.continuous.pow 2).measurable
      (fun x => sq_nonneg (f x)) hζm hζlim
      (δ := fun k : ℕ => (1 / ((k : ℝ) + 1)) * N) (by simpa using hεt.mul_const N)
      (hint _ (hf.continuous.pow 2)) (Eventually.of_forall hA)
    filter_upwards [hz] with x hx
    simpa using hx
  · intro h0
    subst h0
    have hB : ∀ k : ℕ, 1 ≤ k → ∫ x, deriv f x ^ 2 * (ζ k x * ζ k x) ∂G.μ ≤
        2 * (1 / ((k : ℝ) + 1)) * N := by
      intro k hk
      have := hineq k
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hε1 : 1 / ((k : ℝ) + 1) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have hB := hB0 k
      have hε0 : 0 < 1 / ((k : ℝ) + 1) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.2 hε1) hB, mul_nonneg hε0.le hN0]
    have hz := zero_of_cutoff (μ := G.μ) (h := fun x => deriv f x ^ 2) (hf.deriv'.continuous.pow 2).measurable
      (fun x => sq_nonneg (deriv f x)) hζm hζlim
      (δ := fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)) * N)
      (by simpa using (hεt.const_mul 2).mul_const N)
      (hint _ (hf.deriv'.continuous.pow 2))
      (by
        filter_upwards [eventually_ge_atTop 1] with k hk
        exact hB k hk)
    have hc : Continuous (fun x => deriv f x ^ 2) := hf.deriv'.continuous.pow 2
    have hz' : ∀ x, deriv f x ^ 2 = 0 :=
      fun x => congrFun ((hc.ae_eq_iff_eq G.μ continuous_const (g := fun _ => (0 : ℝ))).1 hz) x
    intro x
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (hz' x)

/-- **ESA (F10) for the Gibbs triple, by the book's route** (BGL Prop. 3.2.1 / Cor. 3.2.2): completeness
plus weak hypo-ellipticity at `λ = 1`. -/
theorem gibbsDiff_esaProp (h1 : G.WeakHypoEllipticAt 1) : G.gibbsDiff.ESAProp := by
  refine DiffusionTriple.esaProp_of_orth _ (fun w hw => ?_)
  have hweak : ∀ a ∈ OA₀, ∫ x, w x * Lg G.V a x ∂G.μ = 1 * ∫ x, w x * a x ∂G.μ := by
    intro a ha
    have h := hw ⟨a, ha⟩
    rw [inner_sub_left, sub_eq_zero, DiffusionTriple.inner_cls_eq,
      DiffusionTriple.inner_Lcls_eq] at h
    rw [one_mul]
    exact h.symm
  obtain ⟨f, hfs, hwf⟩ := h1 w hweak
  have hfw : ∀ a ∈ OA₀, ∫ x, f x * Lg G.V a x ∂G.μ = 1 * ∫ x, f x * a x ∂G.μ := by
    intro a ha
    have e1 : ∫ x, f x * Lg G.V a x ∂G.μ = ∫ x, w x * Lg G.V a x ∂G.μ :=
      integral_congr_ae (hwf.mono fun x hx => by dsimp only; rw [← hx]; rfl)
    have e2 : ∫ x, f x * a x ∂G.μ = ∫ x, w x * a x ∂G.μ :=
      integral_congr_ae (hwf.mono fun x hx => by dsimp only; rw [← hx]; rfl)
    rw [e1, e2]; exact hweak a ha
  have hL := G.Lg_eq_of_weak hfs 1 hfw
  have hfL2 : MemLp f 2 G.μ := (Lp.memLp w).ae_eq hwf
  have hf0 := (G.cutoff_conclusion hfs hfL2 1 hL).1 rfl
  have : (w : ℝ → ℝ) =ᵐ[G.μ] 0 := hwf.trans hf0
  exact Lp.eq_zero_iff_ae_eq_zero.2 this

/-- **Ergodicity (S10) for the Gibbs triple, by the book's route** (BGL Prop. 3.3.10): completeness plus
weak hypo-ellipticity at `λ = 0`. -/
theorem gibbsDiff_ergodic (h0 : G.WeakHypoEllipticAt 0) :
    ∀ (u : Lp ℝ 2 G.gibbsDiff.μ) (hu : u ∈ G.gibbsDiff.generator.domain),
      G.gibbsDiff.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[G.gibbsDiff.μ] fun _ => c := by
  intro u hu hGu
  have hweak : ∀ a ∈ OA₀, ∫ x, u x * Lg G.V a x ∂G.μ = 0 * ∫ x, u x * a x ∂G.μ := by
    intro a ha
    have hsym := MarkovTriple.Hilbert.FormData.generator_symm (DiffusionTriple.formData G.gibbsDiff)
      (G.gibbsDiff.cls_mem_generator_domain ⟨a, ha⟩) hu
    have e : (DiffusionTriple.formData G.gibbsDiff).generator
        ⟨G.gibbsDiff.cls ⟨a, ha⟩, G.gibbsDiff.cls_mem_generator_domain ⟨a, ha⟩⟩ =
        G.gibbsDiff.Lcls ⟨a, ha⟩ := G.gibbsDiff.generator_cls ⟨a, ha⟩ _
    rw [e] at hsym
    have hG0 : (DiffusionTriple.formData G.gibbsDiff).generator ⟨u, hu⟩ = 0 := hGu
    rw [hG0, inner_zero_right] at hsym
    rw [DiffusionTriple.inner_Lcls_eq] at hsym
    rw [zero_mul]; exact hsym
  obtain ⟨f, hfs, huf⟩ := h0 u hweak
  have hfw : ∀ a ∈ OA₀, ∫ x, f x * Lg G.V a x ∂G.μ = 0 * ∫ x, f x * a x ∂G.μ := by
    intro a ha
    have e1 : ∫ x, f x * Lg G.V a x ∂G.μ = ∫ x, u x * Lg G.V a x ∂G.μ :=
      integral_congr_ae (huf.mono fun x hx => by dsimp only; rw [← hx]; rfl)
    have e2 : ∫ x, f x * a x ∂G.μ = ∫ x, u x * a x ∂G.μ :=
      integral_congr_ae (huf.mono fun x hx => by dsimp only; rw [← hx]; rfl)
    rw [e1, e2]; exact hweak a ha
  have hL := G.Lg_eq_of_weak hfs 0 hfw
  have hfL2 : MemLp f 2 G.μ := (Lp.memLp u).ae_eq huf
  have hd := (G.cutoff_conclusion hfs hfL2 0 hL).2 rfl
  refine ⟨f 0, huf.trans (Eventually.of_forall fun x => ?_)⟩
  exact is_const_of_deriv_eq_zero (hfs.differentiable (by simp)) hd x 0

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
