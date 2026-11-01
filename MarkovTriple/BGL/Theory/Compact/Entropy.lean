import Mathlib
import MarkovTriple.BGL.Theory.Compact.Gradient
import MarkovTriple.BGL.Theory.Compact.Chain
import MarkovTriple.BGL.Theory.Compact.Smooth

/-!
# `EntropyInterpolation` for every compact triple (de Bruijn identity and `I' = -2J`)

For `φ ∈ 𝒜₀`, `0 ≤ φ ≤ M`, `ε > 0`, `g_s = ε + P_s φ ∈ 𝒜₀` takes values in `[ε, ε+M]`, so
`e(s) = ∫ Θ(g_s)`, `I(s) = -∫ Λ(g_s) L g_s` with the smooth cutoffs `Θ, Λ` of `x log x`, `log`.
The curve `G_s = ε + P_s φ` is `L²`-differentiable with derivative `P_s[Lφ]`, and
`Compact.hasDerivAt_pair` differentiates `∫ F(G_s) V_s` for `F = Θ, Λ`.  The identity `I' = -2J` is
the algebra of `Γ`/`L` chain rules (F6, `k = 1`) and F7.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
open MarkovTriple.BGL.Compact

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace CompactTriple

variable (C : CompactTriple E)

lemma isFinite : IsFiniteMeasure C.μ := by
  have h := C.toDiffusionTriple.memLp (fun _ => (1 : ℝ)) (C.mem_A₀ (C.const_mem_A 1)) 2
    (by norm_num) (by simp)
  rcases (memLp_const_iff (by norm_num) (by simp)).1 h with h | h
  · exact absurd h one_ne_zero
  · exact ⟨h⟩

instance instFinite : IsFiniteMeasure C.μ := C.isFinite

instance instProb : IsProbabilityMeasure C.μ := C.finite_prob C.isFinite

lemma const_mem (c : ℝ) : (fun _ : E => c) ∈ C.A₀ := C.mem_A₀ (C.const_mem_A c)

/-- `L c = 0`. -/
lemma L_const (c : ℝ) : C.L (fun _ : E => c) =ᵐ[C.μ] 0 := by
  have h := C.diffusion_L_A 0 (fun _ => c) contDiff_const (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i)
  filter_upwards [h] with x hx
  simpa using hx

/-- chain rule for `L` on `𝒜`: `L(ψ∘g) = ψ'(g) Lg + ψ''(g) Γ(g)`. -/
lemma L_comp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {g : E → ℝ} (hg : g ∈ C.A) :
    C.L (fun x => ψ (g x)) =ᵐ[C.μ] fun x => deriv ψ (g x) * C.L g x +
      deriv (deriv ψ) (g x) * C.toDiffusionTriple.ΓA g g x := by
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => ψ (z 0)) :=
    hψ.comp (contDiff_apply ℝ ℝ 0)
  have key := C.diffusion_L_A 1 (fun z => ψ (z 0)) hψ' ![g]
    (by intro i; fin_cases i; simpa using hg)
  filter_upwards [key] with x hx
  simp only [Fin.sum_univ_one] at hx
  have hd1 : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hdd : Differentiable ℝ (deriv ψ) :=
    ((contDiff_infty_iff_deriv.1 hψ).2).differentiable (by simp)
  have e1 : pderiv (fun z : Fin 1 → ℝ => ψ (z 0)) 0 (fun j => (![g] : Fin 1 → E → ℝ) j x) =
      deriv ψ (g x) := pderiv_comp_eval ψ hd1 _
  have e2 : pderiv₂ (fun z : Fin 1 → ℝ => ψ (z 0)) 0 0 (fun l => (![g] : Fin 1 → E → ℝ) l x) =
      deriv (deriv ψ) (g x) := by
    unfold pderiv₂
    have : (fun y : Fin 1 → ℝ => pderiv (fun z : Fin 1 → ℝ => ψ (z 0)) 0 y) =
        fun y => deriv ψ (y 0) := funext fun y => pderiv_comp_eval ψ hd1 y
    rw [this]
    exact pderiv_comp_eval (deriv ψ) hdd _
  simp only [Matrix.cons_val_zero] at hx
  rw [hx, e1, e2]

/-- the constant class. -/
noncomputable def constL (c : ℝ) : Lp ℝ 2 C.μ := (memLp_const (p := 2) c).toLp (fun _ => c)

lemma coeFn_constL (c : ℝ) : (C.constL c : E → ℝ) =ᵐ[C.μ] fun _ => c := MemLp.coeFn_toLp _

lemma bdd_constL (c : ℝ) : Bdd |c| (C.constL c) := by
  filter_upwards [C.coeFn_constL c] with x hx; rw [hx]

/-- the `L²` curve `G_s = ε + P_s φ`. -/
noncomputable def entGL (φ : C.A₀) (ε : ℝ) (s : ℝ) : Lp ℝ 2 C.μ := C.constL ε + C.orb φ s

lemma entGL_ae (φ : C.A₀) (ε s : ℝ) :
    (C.entGL φ ε s : E → ℝ) =ᵐ[C.μ] C.toFullTriple.entG φ ε s := by
  filter_upwards [Lp.coeFn_add (C.constL ε) (C.orb φ s), C.coeFn_constL ε, C.orb_ae φ s]
    with x h1 h2 h3
  unfold entGL
  rw [h1]; simp only [Pi.add_apply, h2, h3]; rfl

lemma continuous_entGL (φ : C.A₀) (ε : ℝ) : Continuous (C.entGL φ ε) :=
  continuous_const.add (C.continuous_orb φ)

lemma hasDerivAt_entGL (φ : C.A₀) (ε : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (C.entGL φ ε) (C.orb (C.Lt φ) s) s :=
  (C.hasDerivAt_orb φ hs).const_add _

lemma entG_mem (φ : C.A₀) (ε s : ℝ) : C.toFullTriple.entG φ ε s ∈ C.A₀ :=
  C.mem_A₀ (FullTriple.entG_mem_A C.toFullTriple φ ε s)

lemma L_entG (φ : C.A₀) (ε s : ℝ) :
    C.L (C.toFullTriple.entG φ ε s) =ᵐ[C.μ] (C.orb (C.Lt φ) s : E → ℝ) := by
  have h : C.toFullTriple.entG φ ε s = (fun _ => ε) + C.Pt s.toNNReal φ := rfl
  have h1 := C.toDiffusionTriple.L_add_ae (C.const_mem ε) (C.Pt_mem s.toNNReal φ)
  rw [h]
  filter_upwards [h1, C.L_const ε, C.L_Pt φ s] with x a b c
  rw [a]; simp only [Pi.add_apply, b, c, Pi.zero_apply, zero_add]

lemma L_L_entG (φ : C.A₀) (ε s : ℝ) :
    C.L (C.L (C.toFullTriple.entG φ ε s)) =ᵐ[C.μ] (C.orb (C.Lt (C.Lt φ)) s : E → ℝ) := by
  have h1 : C.L (C.L (C.toFullTriple.entG φ ε s)) =ᵐ[C.μ] C.L (C.Pt s.toNNReal (C.Lt φ)) := by
    refine C.L_congr_A (C.L_mem_A _ (C.A₀_le _ (C.entG_mem φ ε s))) (C.Pt_mem_A _ _) ?_
    exact (C.L_entG φ ε s).trans (C.orb_ae (C.Lt φ) s)
  exact h1.trans (C.L_Pt (C.Lt φ) s)

end CompactTriple

namespace Compact

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

theorem hasDerivAt_pairS {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    {G V : ℝ → Lp ℝ 2 μ} {G' V' : Lp ℝ 2 μ} {s M : ℝ} (hM : 0 ≤ M)
    (hG : HasDerivAt G G' s) (hV : HasDerivAt V V' s) (hVb : ∀ r, Bdd M (V r)) :
    HasDerivAt (fun r => ∫ x, F ((G r : E → ℝ) x) * (V r : E → ℝ) x ∂μ)
      (∫ x, deriv F ((G s : E → ℝ) x) * (G' : E → ℝ) x * (V s : E → ℝ) x ∂μ +
        ∫ x, F ((G s : E → ℝ) x) * (V' : E → ℝ) x ∂μ) s := by
  obtain ⟨K0, K1, K2, h0, h1, h2, b0, b1, b2⟩ := smooth_bounds hF hc
  have hd : Differentiable ℝ F := (contDiff_infty_iff_deriv.1 hF).1
  have hF1 : ContDiff ℝ (⊤ : ℕ∞) (deriv F) := (contDiff_infty_iff_deriv.1 hF).2
  have hd2 : Differentiable ℝ (deriv F) := (contDiff_infty_iff_deriv.1 hF1).1
  exact hasDerivAt_pair hF.continuous hF1.continuous b0 b1 h2 (taylor_of_deriv hd hd2 b2) hM h1
    hG hV hVb

theorem continuousAt_pairS {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    {G V : ℝ → Lp ℝ 2 μ} {s : ℝ} (hG : ContinuousAt G s) (hV : ContinuousAt V s) :
    ContinuousAt (fun r => ∫ x, F ((G r : E → ℝ) x) * (V r : E → ℝ) x ∂μ) s := by
  obtain ⟨K0, K1, K2, h0, h1, h2, b0, b1, b2⟩ := smooth_bounds hF hc
  have hd : Differentiable ℝ F := (contDiff_infty_iff_deriv.1 hF).1
  exact continuousAt_pair hF.continuous b0 (lip_of_deriv hd b1) hG hV

end Compact


namespace CompactTriple

variable (C : CompactTriple E)

section Entropy

variable {C} (φ : C.A₀) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[C.μ] φ.1)
  (hφ : ∀ x, φ.1 x ≤ M) (K : BE.Cut ε M)

include hε hM h0 hφ K

lemma entE_eq (r : ℝ) :
    C.toFullTriple.entE φ ε r = ∫ x, K.Θ (C.entGL φ ε r x) * (C.constL 1 : E → ℝ) x ∂C.μ := by
  unfold FullTriple.entE
  refine integral_congr_ae ?_
  filter_upwards [FullTriple.entG_range C.toFullTriple φ hε hM h0 hφ r, C.entGL_ae φ ε r,
    C.coeFn_constL 1] with x hr h1 h2
  rw [h1, h2, K.Θ_eq hr, mul_one]

lemma entI_eq_neg (s : ℝ) :
    C.toFullTriple.entI φ ε s = -∫ x, K.Λ (C.toFullTriple.entG φ ε s x) *
      C.L (C.toFullTriple.entG φ ε s) x ∂C.μ := by
  set g := C.toFullTriple.entG φ ε s with hg
  have hg0 : g ∈ C.A₀ := C.entG_mem φ ε s
  have hgA : g ∈ C.A := C.A₀_le g hg0
  have hu : (fun x => K.Λ (g x)) ∈ C.A₀ := C.mem_A₀ (C.comp_mem_A K.hΛ hgA)
  have h1 : ∫ x, C.toDiffusionTriple.ΓA g g x / g x ∂C.μ =
      ∫ x, C.toDiffusionTriple.ΓA g (fun x => K.Λ (g x)) x ∂C.μ := by
    refine integral_congr_ae ?_
    filter_upwards [FullTriple.entG_range C.toFullTriple φ hε hM h0 hφ s,
      C.ΓA_comp_left K.hΛ hgA hgA] with x hr h2
    rw [DiffusionTriple.ΓA_comm C.toDiffusionTriple g (fun x => K.Λ (g x))]
    rw [h2, K.deriv_Λ_eq hε hr]
    show _ = (g x)⁻¹ * _
    field_simp
  have h2 := (C.ibp_A g hgA _ hu).1
  show ∫ x, C.toDiffusionTriple.ΓA g g x / g x ∂C.μ = _
  rw [h1, h2]

lemma entI_eq_pair (r : ℝ) :
    C.toFullTriple.entI φ ε r = -∫ x, K.Λ (C.entGL φ ε r x) * (C.orb (C.Lt φ) r : E → ℝ) x ∂C.μ := by
  rw [C.entI_eq_neg φ hε hM h0 hφ K r]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [C.entGL_ae φ ε r, C.L_entG φ ε r] with x h1 h2
  rw [h1, h2]

theorem entE_continuousOn : ContinuousOn (C.toFullTriple.entE φ ε) (Ici 0) := by
  have hf : C.toFullTriple.entE φ ε = fun r => ∫ x, K.Θ (C.entGL φ ε r x) *
      (C.constL 1 : E → ℝ) x ∂C.μ := funext (C.entE_eq φ hε hM h0 hφ K)
  rw [hf]
  intro s _
  exact (continuousAt_pairS K.hΘ K.hΘc (C.continuous_entGL φ ε).continuousAt
    continuousAt_const).continuousWithinAt

theorem entI_continuousOn : ContinuousOn (C.toFullTriple.entI φ ε) (Ici 0) := by
  have hf : C.toFullTriple.entI φ ε = fun r => -∫ x, K.Λ (C.entGL φ ε r x) *
      (C.orb (C.Lt φ) r : E → ℝ) x ∂C.μ := funext (C.entI_eq_pair φ hε hM h0 hφ K)
  rw [hf]
  intro s _
  exact (continuousAt_pairS K.hΛ K.hΛc (C.continuous_entGL φ ε).continuousAt
    (C.continuous_orb (C.Lt φ)).continuousAt).neg.continuousWithinAt

theorem entE_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (C.toFullTriple.entE φ ε) (-C.toFullTriple.entI φ ε s) s := by
  have hf : C.toFullTriple.entE φ ε = fun r => ∫ x, K.Θ (C.entGL φ ε r x) *
      (C.constL 1 : E → ℝ) x ∂C.μ := funext (C.entE_eq φ hε hM h0 hφ K)
  rw [hf]
  have hd := hasDerivAt_pairS K.hΘ K.hΘc (M := |(1 : ℝ)|) (abs_nonneg _)
    (C.hasDerivAt_entGL φ ε hs) (hasDerivAt_const s (C.constL 1)) (fun _ => C.bdd_constL 1)
  refine hd.congr_deriv ?_
  set g := C.toFullTriple.entG φ ε s with hg
  have hg0 : g ∈ C.A₀ := C.entG_mem φ ε s
  have hgA : g ∈ C.A := C.A₀_le g hg0
  have hu : (fun x => K.Λ (g x)) ∈ C.A₀ := C.mem_A₀ (C.comp_mem_A K.hΛ hgA)
  have hLg := C.Lm hg0
  have i1 : ∫ x, deriv K.Θ ((C.entGL φ ε s : E → ℝ) x) * (C.orb (C.Lt φ) s : E → ℝ) x *
      (C.constL 1 : E → ℝ) x ∂C.μ = ∫ x, K.Λ (g x) * C.L g x ∂C.μ + ∫ x, C.L g x ∂C.μ := by
    rw [← integral_add (C.i2 hu hLg) (C.ib hLg)]
    refine integral_congr_ae ?_
    filter_upwards [FullTriple.entG_range C.toFullTriple φ hε hM h0 hφ s, C.entGL_ae φ ε s,
      C.L_entG φ ε s, C.coeFn_constL 1] with x hr h1 h2 h3
    rw [h1, h2, h3]
    have := K.deriv_Θ_eq_Λ hε hr
    simp only [hg] at this ⊢
    rw [this]; ring
  have i2 : ∫ x, K.Θ ((C.entGL φ ε s : E → ℝ) x) * (0 : Lp ℝ 2 C.μ) x ∂C.μ = 0 := by
    have : ∀ᵐ x ∂C.μ, K.Θ ((C.entGL φ ε s : E → ℝ) x) * (0 : Lp ℝ 2 C.μ) x = 0 := by
      filter_upwards [Lp.coeFn_zero ℝ 2 C.μ] with x hx
      rw [hx]; simp
    rw [integral_congr_ae this]; simp
  rw [i1, i2, C.toDiffusionTriple.integral_L g hg0, add_zero, add_zero,
    C.entI_eq_neg φ hε hM h0 hφ K s]
  ring

end Entropy

end CompactTriple


namespace CompactTriple

variable (C : CompactTriple E)

section FisherAlg

variable {ε M : ℝ} (hε : 0 < ε) (K : BE.Cut ε M)

include hε

lemma deriv_deriv_Λ {y : ℝ} (hy : y ∈ Icc ε (ε + M)) :
    deriv (deriv K.Λ) y = -(y ^ 2)⁻¹ := by
  have h : deriv K.Λ =ᶠ[𝓝 y] fun x => x⁻¹ := by
    have := (K.hΛeq y hy).deriv
    rw [Real.deriv_log'] at this
    exact this
  rw [h.deriv_eq, deriv_inv]

/-- **`I' = -2J` algebra**: for `g ∈ 𝒜₀` with values in `[ε, ε+M]` and `u = Λ∘g`,
`∫ Λ'(g)(Lg)² + ∫ Λ(g) L(Lg) = 2 ∫ g Γ₂(u)`. -/
theorem fisher_alg {g : E → ℝ} (hg0 : g ∈ C.A₀) (hr : ∀ᵐ x ∂C.μ, g x ∈ Icc ε (ε + M)) :
    ∫ x, deriv K.Λ (g x) * C.L g x * C.L g x ∂C.μ + ∫ x, K.Λ (g x) * C.L (C.L g) x ∂C.μ =
      2 * ∫ x, g x * C.toDiffusionTriple.Γ₂ (fun y => K.Λ (g y)) (fun y => K.Λ (g y)) x ∂C.μ := by
  have hgA : g ∈ C.A := C.A₀_le g hg0
  have hΛ1 : ContDiff ℝ (⊤ : ℕ∞) (deriv K.Λ) := (contDiff_infty_iff_deriv.1 K.hΛ).2
  have hΛ2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv K.Λ)) := (contDiff_infty_iff_deriv.1 hΛ1).2
  have hu : (fun x => K.Λ (g x)) ∈ C.A₀ := C.mem_A₀ (C.comp_mem_A K.hΛ hgA)
  have ha : (fun x => deriv K.Λ (g x)) ∈ C.A₀ := C.mem_A₀ (C.comp_mem_A hΛ1 hgA)
  have hb : (fun x => deriv (deriv K.Λ) (g x)) ∈ C.A₀ := C.mem_A₀ (C.comp_mem_A hΛ2 hgA)
  have hLg := C.Lm hg0
  have hLLg := C.Lm hLg
  have hX : C.toDiffusionTriple.ΓA g g ∈ C.A₀ := C.ΓA_self_mem_A₀ hg0
  have hLu := C.Lm hu
  have hY : C.toDiffusionTriple.ΓA (fun x => K.Λ (g x)) (fun x => K.Λ (g x)) ∈ C.A₀ :=
    C.ΓA_self_mem_A₀ hu
  -- a.e. facts
  have f1 := C.L_comp K.hΛ hgA
  have f2 := C.ΓA_comp_comp K.hΛ hgA
  have f3 := C.ΓA_comp_left K.hΛ hgA (C.A₀_le _ hLu)
  have f4 : ∀ᵐ x ∂C.μ, g x * deriv K.Λ (g x) = 1 := by
    filter_upwards [hr] with x hx
    rw [K.deriv_Λ_eq hε hx]
    have : g x ≠ 0 := by linarith [hx.1]
    field_simp
  have f5 : ∀ᵐ x ∂C.μ, deriv K.Λ (g x) ^ 2 + deriv (deriv K.Λ) (g x) = 0 := by
    filter_upwards [hr] with x hx
    rw [K.deriv_Λ_eq hε hx, deriv_deriv_Λ hε K hx, inv_pow]; ring
  -- (i) ∫ g L Y = ∫ a² X Lg
  have s1 : ∫ x, g x * C.L (C.toDiffusionTriple.ΓA (fun x => K.Λ (g x)) (fun x => K.Λ (g x))) x ∂C.μ
      = ∫ x, deriv K.Λ (g x) ^ 2 * C.toDiffusionTriple.ΓA g g x * C.L g x ∂C.μ := by
    rw [C.sym hg0 hY]
    refine integral_congr_ae ?_
    filter_upwards [f2] with x hx
    rw [hx]
  -- (ii) ∫ g ΓA u (Lu) = - ∫ Lu Lg
  have s2 : ∫ x, g x * C.toDiffusionTriple.ΓA (fun x => K.Λ (g x)) (C.L fun x => K.Λ (g x)) x ∂C.μ
      = -∫ x, C.L (fun x => K.Λ (g x)) x * C.L g x ∂C.μ := by
    have := (C.ibp_A g hgA _ hLu).1
    rw [show -∫ x, C.L (fun x => K.Λ (g x)) x * C.L g x ∂C.μ =
      -∫ x, C.L (fun x => K.Λ (g x)) x * C.L g x ∂C.μ from rfl, ← this]
    refine integral_congr_ae ?_
    filter_upwards [f3, f4, DiffusionTriple.ΓA_comm C.toDiffusionTriple g (C.L fun x => K.Λ (g x))
      |> fun h => Eventually.of_forall (fun x => congrFun h x)] with x h1 h2 h3
    rw [h1, ← mul_assoc, h2, one_mul]
  have s3 : ∫ x, K.Λ (g x) * C.L (C.L g) x ∂C.μ =
      ∫ x, C.L (fun x => K.Λ (g x)) x * C.L g x ∂C.μ :=
    (C.sym hu hLg).trans (integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _))
  -- the three basic integrals
  have iA : Integrable (fun x => deriv K.Λ (g x) * C.L g x * C.L g x) C.μ := C.i3 ha hLg hLg
  have iB : Integrable (fun x => deriv (deriv K.Λ) (g x) * C.toDiffusionTriple.ΓA g g x *
      C.L g x) C.μ := C.i3 hb hX hLg
  have iC : Integrable (fun x => deriv K.Λ (g x) ^ 2 * C.toDiffusionTriple.ΓA g g x *
      C.L g x) C.μ := by
    have := C.i3 (C.A₀.mul_mem ha ha) hX hLg
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  have eLu : ∫ x, C.L (fun x => K.Λ (g x)) x * C.L g x ∂C.μ =
      ∫ x, deriv K.Λ (g x) * C.L g x * C.L g x ∂C.μ +
        ∫ x, deriv (deriv K.Λ) (g x) * C.toDiffusionTriple.ΓA g g x * C.L g x ∂C.μ := by
    rw [← integral_add iA iB]
    refine integral_congr_ae ?_
    filter_upwards [f1] with x hx
    rw [hx]; ring
  have hz : ∫ x, deriv K.Λ (g x) ^ 2 * C.toDiffusionTriple.ΓA g g x * C.L g x ∂C.μ +
      ∫ x, deriv (deriv K.Λ) (g x) * C.toDiffusionTriple.ΓA g g x * C.L g x ∂C.μ = 0 := by
    rw [← integral_add iC iB]
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [f5] with x hx
      have : (deriv K.Λ (g x) ^ 2 * C.toDiffusionTriple.ΓA g g x * C.L g x) +
          deriv (deriv K.Λ) (g x) * C.toDiffusionTriple.ΓA g g x * C.L g x =
          (deriv K.Λ (g x) ^ 2 + deriv (deriv K.Λ) (g x)) *
            (C.toDiffusionTriple.ΓA g g x * C.L g x) := by ring
      simp only [this, hx, zero_mul]
  -- the Γ₂ integral
  have e1 : 2 * ∫ x, g x * C.toDiffusionTriple.Γ₂ (fun y => K.Λ (g y)) (fun y => K.Λ (g y)) x ∂C.μ =
      ∫ x, g x * C.L (C.toDiffusionTriple.ΓA (fun x => K.Λ (g x)) (fun x => K.Λ (g x))) x ∂C.μ -
        2 * ∫ x, g x * C.toDiffusionTriple.ΓA (fun x => K.Λ (g x)) (C.L fun x => K.Λ (g x)) x
          ∂C.μ := by
    have hΓ := C.ΓA_mem_A₀ (C.A₀_le _ hu) hLu
    have j1 := C.i2 hg0 (C.Lm hY)
    have j2 := C.i2 hg0 hΓ
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub j1 (j2.const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [DiffusionTriple.Γ₂]
    rw [DiffusionTriple.ΓA_comm C.toDiffusionTriple (C.L fun x => K.Λ (g x)) (fun x => K.Λ (g x))]
    ring
  rw [e1, s1, s2, eLu, s3, eLu]
  linarith

end FisherAlg

end CompactTriple


namespace CompactTriple

variable (C : CompactTriple E)

section FisherDeriv

variable {C} (φ : C.A₀) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[C.μ] φ.1)
  (hφ : ∀ x, φ.1 x ≤ M) (K : BE.Cut ε M)

include hε hM h0 hφ K

theorem entI_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (C.toFullTriple.entI φ ε) (-2 * C.toFullTriple.entJ K.Λ φ ε s) s := by
  have hf : C.toFullTriple.entI φ ε = fun r => -∫ x, K.Λ (C.entGL φ ε r x) *
      (C.orb (C.Lt φ) r : E → ℝ) x ∂C.μ := funext (C.entI_eq_pair φ hε hM h0 hφ K)
  rw [hf]
  obtain ⟨c, hc, hb⟩ := C.orb_bdd' (C.Lt φ)
  have hd := hasDerivAt_pairS K.hΛ K.hΛc hc.le (C.hasDerivAt_entGL φ ε hs)
    (C.hasDerivAt_orb (C.Lt φ) hs) hb
  refine hd.neg.congr_deriv ?_
  set g := C.toFullTriple.entG φ ε s with hg
  have hg0 : g ∈ C.A₀ := C.entG_mem φ ε s
  have hrange := FullTriple.entG_range C.toFullTriple φ hε hM h0 hφ s
  have e1 : ∫ x, deriv K.Λ ((C.entGL φ ε s : E → ℝ) x) * (C.orb (C.Lt φ) s : E → ℝ) x *
      (C.orb (C.Lt φ) s : E → ℝ) x ∂C.μ = ∫ x, deriv K.Λ (g x) * C.L g x * C.L g x ∂C.μ := by
    refine integral_congr_ae ?_
    filter_upwards [C.entGL_ae φ ε s, C.L_entG φ ε s] with x h1 h2
    rw [h1, h2]
  have e2 : ∫ x, K.Λ ((C.entGL φ ε s : E → ℝ) x) * (C.orb (C.Lt (C.Lt φ)) s : E → ℝ) x ∂C.μ =
      ∫ x, K.Λ (g x) * C.L (C.L g) x ∂C.μ := by
    refine integral_congr_ae ?_
    filter_upwards [C.entGL_ae φ ε s, C.L_L_entG φ ε s] with x h1 h2
    rw [h1, h2]
  rw [e1, e2, C.fisher_alg hε K hg0 hrange]
  unfold FullTriple.entJ
  ring

theorem entJ_integrable (s : ℝ) :
    Integrable (fun x => C.toFullTriple.entG φ ε s x * C.toDiffusionTriple.Γ₂
      (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) x)
      C.μ ∧
    Integrable (fun x => C.toFullTriple.entG φ ε s x * C.toDiffusionTriple.ΓA
      (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) x)
      C.μ := by
  have hg0 : C.toFullTriple.entG φ ε s ∈ C.A₀ := C.entG_mem φ ε s
  have hu : (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) ∈ C.A₀ :=
    C.mem_A₀ (C.comp_mem_A K.hΛ (C.A₀_le _ hg0))
  exact ⟨C.i2 hg0 (C.Γ₂_mem hu), C.i2 hg0 (C.ΓA_self_mem_A₀ hu)⟩

end FisherDeriv

lemma exists_data (φ : C.A₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ (∀ x, φ.1 x ≤ M) ∧ Nonempty (BE.Cut ε M) := by
  obtain ⟨c, hc, h⟩ := C.exists_bound φ
  exact ⟨c, hc, fun x => (le_abs_self _).trans (h x), BE.exists_cut hε hc.le⟩

/-- **`EntropyInterpolation` holds for every compact triple.** -/
theorem entropyInterpolation : C.toFullTriple.EntropyInterpolation where
  continuousOn_E := fun φ ε hε h0 => by
    obtain ⟨M, hM, hφ, ⟨K⟩⟩ := C.exists_data φ hε
    exact C.entE_continuousOn φ hε hM h0 hφ K
  continuousOn_I := fun φ ε hε h0 => by
    obtain ⟨M, hM, hφ, ⟨K⟩⟩ := C.exists_data φ hε
    exact C.entI_continuousOn φ hε hM h0 hφ K
  hasDerivAt_E := fun φ ε hε h0 s hs => by
    obtain ⟨M, hM, hφ, ⟨K⟩⟩ := C.exists_data φ hε
    exact C.entE_hasDerivAt φ hε hM h0 hφ K hs
  hasDerivAt_I := fun φ ε M hε hM h0 hφ K s hs =>
    ⟨(C.entJ_integrable φ hε hM h0 hφ K s).1, (C.entJ_integrable φ hε hM h0 hφ K s).2,
      C.entI_hasDerivAt φ hε hM h0 hφ K hs⟩

end CompactTriple

/-- Compact triples satisfy the regularity hypothesis `EntropyInterpolation` (G3 of `GAPS.md`). -/
theorem compact_entropyInterpolation (C : CompactTriple E) :
    C.toFullTriple.EntropyInterpolation := C.entropyInterpolation

end MarkovTriple.BGL
