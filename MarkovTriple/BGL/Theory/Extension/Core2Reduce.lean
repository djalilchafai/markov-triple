import Mathlib
import MarkovTriple.BGL.Theory.Extension.Converse
import MarkovTriple.BGL.Frozen.CompactTriple

/-!
# `Core2` reduces to density of `(1 − L)² 𝒜₀` in `L²`; compact triples

Statements: `Extension/STATEMENTS_R15_Core2.md`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- `b ↦ [b] − 2[L b] + [L L b] = (1 − L)² b`, `𝒜₀ → L²`. -/
noncomputable def Ψₗ (T : FullTriple E) : T.A₀ →ₗ[ℝ] Lp ℝ 2 T.μ :=
  Φₗ T - (DiffusionTriple.Lclsₗ T.toDiffusionTriple - LLₗ T)

/-- `(1 − L) b ∈ 𝒜₀` for `b ∈ 𝒜₀`. -/
def Iₐ (T : FullTriple E) (b : T.A₀) : T.A₀ :=
  ⟨fun x => b.1 x - T.L b.1 x, T.A₀.sub_mem b.2 (T.L_mem b.1 b.2)⟩

lemma cls_Iₐ (b : T.A₀) :
    T.toDiffusionTriple.cls (Iₐ T b) = T.toDiffusionTriple.cls b - T.toDiffusionTriple.Lcls b := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (T.toDiffusionTriple.cls b) (T.toDiffusionTriple.Lcls b),
    DiffusionTriple.coeFn_cls T.toDiffusionTriple b, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b,
    DiffusionTriple.coeFn_cls T.toDiffusionTriple (Iₐ T b)] with x e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, e4]; rfl

lemma Lcls_Iₐ (b : T.A₀) :
    T.toDiffusionTriple.Lcls (Iₐ T b) = T.toDiffusionTriple.Lcls b - LLₗ T b := by
  have hbA := T.A₀_le _ b.2
  have hLb := T.L_mem_A _ hbA
  have hu : (fun x => b.1 x - T.L b.1 x) = fun x => b.1 x + (-1 : ℝ) * T.L b.1 x := by funext x; ring
  have h2 := L_lin hbA hLb (-1 : ℝ)
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (T.toDiffusionTriple.Lcls b) (LLₗ T b),
    DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b,
    DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀),
    DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (Iₐ T b), h2] with x e1 e2 e3 e4 e5
  rw [e1, Pi.sub_apply, e2]
  have e3' : ((LLₗ T b : Lp ℝ 2 T.μ) : E → ℝ) x = T.L (T.L b.1) x := e3
  rw [e3', e4]
  show T.L (fun x => b.1 x - T.L b.1 x) x = _
  rw [hu, e5]; ring

lemma Φₗ_Iₐ (b : T.A₀) : Φₗ T (Iₐ T b) = Ψₗ T b := by
  rw [Φₗ_apply, cls_Iₐ, Lcls_Iₐ]
  show _ = (Φₗ T b) - (T.toDiffusionTriple.Lcls b - LLₗ T b)
  rw [Φₗ_apply]

/-- `‖[c]‖, ‖[L c]‖ ≤ ‖[c] − [L c]‖` for `c ∈ 𝒜₀` (F5, F7: `⟪[c],[Lc]⟫ = −∫Γ(c) ≤ 0`). -/
lemma norm_le_Φ (c : T.A₀) :
    ‖T.toDiffusionTriple.cls c‖ ≤ ‖Φₗ T c‖ ∧ ‖T.toDiffusionTriple.Lcls c‖ ≤ ‖Φₗ T c‖ := by
  have hb := c.2
  have hbA := T.A₀_le _ hb
  set x : Lp ℝ 2 T.μ := T.toDiffusionTriple.cls c with hx
  set y : Lp ℝ 2 T.μ := T.toDiffusionTriple.Lcls c with hy
  set N : ℝ := ‖Φₗ T c‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hΦ : Φₗ T c = x - y := rfl
  have hxy : inner ℝ x y = ∫ t, c.1 t * T.L c.1 t ∂T.μ := inner_cls_Lcls c c
  have hGbb : ∫ t, G T c.1 c.1 t ∂T.μ = -∫ t, c.1 t * T.L c.1 t ∂T.μ := (T.ibp_A c.1 hbA c.1 hb).2
  have hGnn : 0 ≤ ∫ t, G T c.1 c.1 t ∂T.μ := integral_nonneg_of_ae (T.ΓA_nonneg c.1 hbA)
  have hxy0 : inner ℝ x y ≤ 0 := by rw [hxy]; linarith
  have hN2 : N ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
    rw [hN, hΦ]; exact norm_sub_sq_real x y
  constructor
  · by_contra hc; replace hc := not_le.mp hc
    nlinarith [norm_nonneg x, norm_nonneg y]
  · by_contra hc; replace hc := not_le.mp hc
    nlinarith [norm_nonneg x, norm_nonneg y]

/-- **Reduction of `Core2` to density**: if `(1 − L)²𝒜₀` is dense in `L²` then `Core2` holds. -/
theorem core2_of_dense (hd : Dense (Set.range (Ψₗ T))) : T.Core2 := by
  intro a
  obtain ⟨m, hm, hmz⟩ := mem_closure_iff_seq_limit.1 (hd.closure_eq ▸ Set.mem_univ (Φₗ T a))
  choose b hb using hm
  have hc : ∀ n, Φₗ T (Iₐ T (b n) - a) = m n - Φₗ T a := fun n => by
    rw [map_sub, Φₗ_Iₐ, hb n]
  have hlim : Tendsto (fun n => ‖Φₗ T (Iₐ T (b n) - a)‖) atTop (𝓝 0) := by
    have := (hmz.sub_const (Φₗ T a)).norm
    simp only [sub_self, norm_zero] at this
    exact this.congr (fun n => by rw [hc n])
  have h1 : Tendsto (fun n => ‖T.toDiffusionTriple.cls (Iₐ T (b n) - a)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (norm_le_Φ _).1) hlim
  have h2 : Tendsto (fun n => ‖T.toDiffusionTriple.Lcls (Iₐ T (b n) - a)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (norm_le_Φ _).2) hlim
  refine ⟨b, ?_, ?_⟩
  · have : Tendsto (fun n => T.toDiffusionTriple.cls (Iₐ T (b n))) atTop (𝓝 (T.toDiffusionTriple.cls a)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine h1.congr fun n => ?_
      rw [show T.toDiffusionTriple.cls (Iₐ T (b n) - a) =
        T.toDiffusionTriple.cls (Iₐ T (b n)) - T.toDiffusionTriple.cls a from
          map_sub (DiffusionTriple.clsₗ T.toDiffusionTriple) _ _]
    exact this.congr fun n => cls_Iₐ (b n)
  · have : Tendsto (fun n => T.toDiffusionTriple.Lcls (Iₐ T (b n))) atTop
        (𝓝 (T.toDiffusionTriple.Lcls a)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine h2.congr fun n => ?_
      rw [show T.toDiffusionTriple.Lcls (Iₐ T (b n) - a) =
        T.toDiffusionTriple.Lcls (Iₐ T (b n)) - T.toDiffusionTriple.Lcls a from
          map_sub (DiffusionTriple.Lclsₗ T.toDiffusionTriple) _ _]
    exact this.congr fun n => Lcls_Iₐ (b n)

end FullTriple

/-! ### Compact triples (`𝒜 = 𝒜₀`): the converse is unconditional -/

namespace CompactTriple

variable (C : CompactTriple E)

/-- For a compact triple every `f ∈ 𝒜 = 𝒜₀` is a test function, so `[f] ∈ 𝒟(L)`, `L[f] = [Lf]`: the converse of
Prop. 3.3.17 holds with no `Core2`, no curvature hypothesis, no integrability hypothesis. -/
theorem mem_domain_of_A {f : E → ℝ} (hf : f ∈ C.A) (hf2 : MemLp f 2 C.μ) :
    ∃ hF : hf2.toLp f ∈ C.toDiffusionTriple.generator.domain,
      ((C.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 C.μ) : E → ℝ) =ᵐ[C.μ] C.L f := by
  have hf0 : f ∈ C.A₀ := (C.A_eq f).1 hf
  have e : hf2.toLp f = C.toDiffusionTriple.cls ⟨f, hf0⟩ := by
    refine Lp.ext ?_
    filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨f, hf0⟩] with x h1 h2
    rw [h1, h2]
  have hF : hf2.toLp f ∈ C.toDiffusionTriple.generator.domain := by
    rw [e]; exact DiffusionTriple.cls_mem_generator_domain _ _
  exact ⟨hF, FullTriple.generator_ae_L (T := C.toFullTriple) hf hf2 hF⟩

end CompactTriple

end MarkovTriple.BGL
