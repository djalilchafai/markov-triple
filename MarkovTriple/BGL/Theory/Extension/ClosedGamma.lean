import Mathlib
import MarkovTriple.BGL.Theory.Extension.ClosedBasic
import MarkovTriple.BGL.Calculus.Density

/-!
# `Γ` on `𝒟(ℰ)`: definition and basic properties (BGL Prop. 3.1.5 / (3.1.10), as used in Prop. 3.3.5 (ii))

* `jE : 𝒜₀ → K`, `K` = the Hilbert completion of `𝒜₀` for `(‖·‖₂² + ℰ)^{1/2}` (the book's `𝒟(ℰ)` with its Hilbert
  topology, D7), `‖jE a‖² = ‖[a]‖² + ∫Γ(a)`.
* `FormConv a u`: `a_k → u` in `𝒟(ℰ)` (form-norm convergence of test functions).
* `gammaE u v ∈ L¹`: the limit of `Γ(a_k,b_k)` along any form-convergent sequences (`gammaE_tendsto`), with
  `gammaE (cls a) (cls b) = [Γ(a,b)]`, `∫ gammaE u v = ℰ(u,v)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- the Hilbert space of `𝒟(ℰ)` (completion of `𝒜₀` in the form norm). -/
abbrev KE (T : FullTriple E) : Type _ := (DiffusionTriple.formData T.toDiffusionTriple).K

/-- the class of a test function as an element of the dense domain `D` of the Friedrichs form. -/
noncomputable def domElt (T : FullTriple E) (a : T.A₀) : (DiffusionTriple.formData T.toDiffusionTriple).Dom :=
  ⟨DiffusionTriple.clsₗ T.toDiffusionTriple a, ⟨a, rfl⟩⟩

/-- the embedding `𝒜₀ → K` (the class of a test function in `𝒟(ℰ)` with its Hilbert norm). -/
noncomputable def jE (T : FullTriple E) : T.A₀ →+ KE T where
  toFun a := ((domElt T a : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T)
  map_zero' := by
    have : domElt T 0 = 0 := by
      apply Subtype.ext
      show DiffusionTriple.clsₗ T.toDiffusionTriple 0 = 0
      simp
    rw [this]; rfl
  map_add' a b := by
    have : domElt T (a + b) = domElt T a + domElt T b := by
      apply Subtype.ext
      show DiffusionTriple.clsₗ T.toDiffusionTriple (a + b) =
        DiffusionTriple.clsₗ T.toDiffusionTriple a + DiffusionTriple.clsₗ T.toDiffusionTriple b
      simp
    show ((domElt T (a + b) : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T) =
      ((domElt T a : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T) +
      ((domElt T b : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T)
    rw [this, UniformSpace.Completion.coe_add]

lemma ι_jE (a : T.A₀) : (DiffusionTriple.formData T.toDiffusionTriple).ι (jE T a) =
    T.toDiffusionTriple.cls a := by
  show (DiffusionTriple.formData T.toDiffusionTriple).ι
    ((domElt T a : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T) = _
  rw [Hilbert.FormData.ι_coe]; rfl

lemma norm_jE_sq (a : T.A₀) :
    ‖jE T a‖ ^ 2 = ‖T.toDiffusionTriple.cls a‖ ^ 2 + ∫ x, G T a.1 a.1 x ∂T.μ := by
  have h1 : ‖jE T a‖ ^ 2 = inner ℝ (jE T a) (jE T a) := (real_inner_self_eq_norm_sq _).symm
  show ‖((domElt T a : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T)‖ ^ 2 = _
  rw [UniformSpace.Completion.norm_coe, ← real_inner_self_eq_norm_sq,
    Hilbert.FormData.inner_dom]
  have e1 : inner ℝ ((DiffusionTriple.formData T.toDiffusionTriple).emb (domElt T a))
      ((DiffusionTriple.formData T.toDiffusionTriple).emb (domElt T a)) =
      ‖T.toDiffusionTriple.cls a‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]; rfl
  have e2 : inner ℝ ((DiffusionTriple.formData T.toDiffusionTriple).opA (domElt T a))
      ((DiffusionTriple.formData T.toDiffusionTriple).emb (domElt T a)) =
      ∫ x, G T a.1 a.1 x ∂T.μ := by
    have := DiffusionTriple.inner_formA T.toDiffusionTriple a a
    refine this.trans ?_
    unfold DiffusionTriple.qf
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.ΓA_ae_eq T.toDiffusionTriple a.2 a.2] with x hx
    exact hx.symm
  rw [e1, e2]

lemma int_G_le_norm_jE (a : T.A₀) : ∫ x, G T a.1 a.1 x ∂T.μ ≤ ‖jE T a‖ ^ 2 := by
  rw [norm_jE_sq]; nlinarith [sq_nonneg ‖T.toDiffusionTriple.cls a‖]

/-- `a_k → u` in `𝒟(ℰ)` for the Hilbert topology `(‖·‖₂² + ℰ)^{1/2}` of the book (Sect. 3.1):
`jE(a_k) → u` in the Hilbert space `K`. -/
def FormConv (T : FullTriple E) (a : ℕ → T.A₀) (u : T.formDomain) : Prop :=
  Tendsto (fun k => jE T (a k)) atTop
    (𝓝 ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u))

lemma qEquiv_jE (a : T.A₀) : (DiffusionTriple.formData T.toDiffusionTriple).qEquiv (jE T a) =
    T.toDiffusionTriple.clsQ a := by
  apply Subtype.ext
  rw [Hilbert.FormData.qEquiv_apply, ι_jE]; rfl

lemma formConv_const (a : T.A₀) : FormConv T (fun _ => a) (T.toDiffusionTriple.clsQ a) := by
  unfold FormConv
  have : (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm (T.toDiffusionTriple.clsQ a) =
      jE T a := by
    rw [← qEquiv_jE]; simp
  rw [this]; exact tendsto_const_nhds

/-- every `u ∈ 𝒟(ℰ)` is a form-limit of test functions (density of `𝒜₀`, D7). -/
lemma exists_formConv (u : T.formDomain) : ∃ a : ℕ → T.A₀, FormConv T a u := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  set x := S.qEquiv.symm u with hx
  have hxc : x ∈ closure (Set.range ((↑) : S.Dom → S.K)) :=
    UniformSpace.Completion.denseRange_coe x
  obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.1 hxc
  have hs' : ∀ n, ∃ a : T.A₀, jE T a = s n := by
    intro n
    obtain ⟨d, hd⟩ := hs n
    obtain ⟨_, a, rfl⟩ := d
    exact ⟨a, hd⟩
  choose a ha using hs'
  refine ⟨a, ?_⟩
  have : (fun k => jE T (a k)) = s := funext ha
  unfold FormConv
  rw [this]; exact hslim

lemma FormConv.cls {a : ℕ → T.A₀} {u : T.formDomain} (h : FormConv T a u) :
    Tendsto (fun k => T.toDiffusionTriple.cls (a k)) atTop (𝓝 (u : Lp ℝ 2 T.μ)) := by
  have := ((DiffusionTriple.formData T.toDiffusionTriple).ι.continuous.tendsto _).comp h
  have e : (DiffusionTriple.formData T.toDiffusionTriple).ι
      ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u) = u := by
    have := Hilbert.FormData.qEquiv_apply (DiffusionTriple.formData T.toDiffusionTriple)
      ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u)
    have h1 := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.apply_symm_apply u
    rw [h1] at this
    exact this.symm
  rw [e] at this
  exact this.congr (fun k => ι_jE (a k))

lemma coe_sub' (a b : T.A₀) : ((a - b : T.A₀) : E → ℝ) = fun x => a.1 x + (-1) * b.1 x := by
  funext x
  show a.1 x - b.1 x = _
  ring

/-- the `L¹`-class of `Γ(a,b)`, `a, b ∈ 𝒜₀`. -/
noncomputable def GG (T : FullTriple E) (a b : T.A₀) : Lp ℝ 1 T.μ :=
  (integrable_A₀ (ΓA_mem_A₀ T (A₀_memA a.2) b.2)).toL1 (G T a.1 b.1)

lemma GG_ae (a b : T.A₀) : (GG T a b : E → ℝ) =ᵐ[T.μ] G T a.1 b.1 :=
  Integrable.coeFn_toL1 _

lemma GG_comm (a b : T.A₀) : GG T a b = GG T b a := by
  refine Lp.ext ?_
  filter_upwards [GG_ae a b, GG_ae b a] with x h1 h2
  rw [h1, h2, G_comm]

lemma GG_sub_left (a a' b : T.A₀) : GG T (a - a') b = GG T a b - GG T a' b := by
  refine Lp.ext ?_
  filter_upwards [GG_ae (a - a') b, GG_ae a b, GG_ae a' b, Lp.coeFn_sub (GG T a b) (GG T a' b),
    G_lin_left (A₀_memA a.2) (A₀_memA a'.2) (-1) (A₀_memA b.2)] with x h1 h2 h3 h4 h5
  rw [h4, Pi.sub_apply, h1, h2, h3, coe_sub']
  rw [h5]; ring

lemma GG_sub_right (a b b' : T.A₀) : GG T a (b - b') = GG T a b - GG T a b' := by
  rw [GG_comm, GG_sub_left, GG_comm b a, GG_comm b' a]

lemma norm_GG (a b : T.A₀) : ‖GG T a b‖ = ∫ x, |G T a.1 b.1 x| ∂T.μ := by
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [GG_ae a b] with x hx
  rw [hx]; rfl

lemma G_cs_A₀ (a b : T.A₀) :
    ∀ᵐ x ∂T.μ, (G T a.1 b.1 x) ^ 2 ≤ G T a.1 a.1 x * G T b.1 b.1 x :=
  ExtendedAlgebra.ΓA_cs T.extendedAlgebra (A₀_memA a.2) (A₀_memA b.2)

lemma integrable_G (a b : T.A₀) : Integrable (G T a.1 b.1) T.μ :=
  integrable_A₀ (ΓA_mem_A₀ T (A₀_memA a.2) b.2)

/-- `∫|Γ(a,b)| ≤ √ℰ(a) √ℰ(b)`. -/
lemma int_abs_G_le (a b : T.A₀) :
    ∫ x, |G T a.1 b.1 x| ∂T.μ ≤ √(∫ x, G T a.1 a.1 x ∂T.μ) * √(∫ x, G T b.1 b.1 x ∂T.μ) :=
  (int_abs_le_sqrt (integrable_G a a) (integrable_G b b) (integrable_G a b).1
    (T.ΓA_nonneg _ (A₀_memA a.2)) (T.ΓA_nonneg _ (A₀_memA b.2)) (G_cs_A₀ a b)).2

lemma norm_GG_le (a b : T.A₀) : ‖GG T a b‖ ≤ 1 * ‖jE T a‖ * ‖jE T b‖ := by
  rw [norm_GG, one_mul]
  refine (int_abs_G_le a b).trans ?_
  have h1 : √(∫ x, G T a.1 a.1 x ∂T.μ) ≤ ‖jE T a‖ :=
    Real.sqrt_le_iff.2 ⟨norm_nonneg _, int_G_le_norm_jE a⟩
  have h2 : √(∫ x, G T b.1 b.1 x ∂T.μ) ≤ ‖jE T b‖ :=
    Real.sqrt_le_iff.2 ⟨norm_nonneg _, int_G_le_norm_jE b⟩
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (norm_nonneg _)

/-- **Existence of `Γ` on `𝒟(ℰ)`** (BGL Prop. 3.1.5 / (3.1.10)): the images `Γ(a_k,b_k) ∈ L¹` converge, and the
limit does not depend on the form-convergent approximating sequences. -/
theorem gammaE_exists (u v : T.formDomain) :
    ∃ γ : Lp ℝ 1 T.μ, ∀ (a b : ℕ → T.A₀), FormConv T a u → FormConv T b v →
      Tendsto (fun k => GG T (a k) (b k)) atTop (𝓝 γ) := by
  obtain ⟨a0, ha0⟩ := exists_formConv u
  obtain ⟨b0, hb0⟩ := exists_formConv v
  exact bil_spec (jE T) (jE T) (GG T) zero_le_one (fun x x' y => GG_sub_left x x' y)
    (fun x y y' => GG_sub_right x y y') norm_GG_le ⟨a0, b0, ha0, hb0⟩

/-- **`Γ` on `𝒟(ℰ)`** (BGL Prop. 3.1.5 / (3.1.10)): `Γ(u,v) ∈ L¹(μ)`. -/
noncomputable def gammaE (T : FullTriple E) (u v : T.formDomain) : Lp ℝ 1 T.μ :=
  Classical.choose (gammaE_exists u v)

theorem gammaE_tendsto {u v : T.formDomain} {a b : ℕ → T.A₀} (ha : FormConv T a u)
    (hb : FormConv T b v) : Tendsto (fun k => GG T (a k) (b k)) atTop (𝓝 (gammaE T u v)) :=
  Classical.choose_spec (gammaE_exists u v) a b ha hb

theorem gammaE_cls (a b : T.A₀) :
    gammaE T (T.toDiffusionTriple.clsQ a) (T.toDiffusionTriple.clsQ b) = GG T a b :=
  tendsto_nhds_unique (gammaE_tendsto (formConv_const a) (formConv_const b)) tendsto_const_nhds

theorem gammaE_comm (u v : T.formDomain) : gammaE T u v = gammaE T v u := by
  obtain ⟨a, ha⟩ := exists_formConv u
  obtain ⟨b, hb⟩ := exists_formConv v
  refine tendsto_nhds_unique (gammaE_tendsto ha hb) ?_
  have := gammaE_tendsto hb ha
  exact this.congr (fun k => GG_comm _ _)

end FullTriple

end MarkovTriple.BGL
