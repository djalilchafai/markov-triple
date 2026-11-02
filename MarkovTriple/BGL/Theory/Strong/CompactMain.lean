import Mathlib
import MarkovTriple.BGL.Theory.Strong.CompactCurve
import MarkovTriple.BGL.Theory.Strong.Main
import MarkovTriple.BGL.Theory.Compact.Smooth

/-!
# `StrongInterpolation` for every compact triple, hence BGL Thm 3.3.18 on compact triples

Assembly: with `u_r = [Γ(P_{t-r} f)]` (`L²`-differentiable, `0 ≤ u_r ≤ B`), `V_r = P_r h`, and
`F` a compactly supported smooth function equal to `ψ_ε` on `[-(B+1), B+1]`, `r ↦ ∫ F(u_r) V_r` is
differentiable (`Compact.hasDerivAt_pair`) with derivative `∫ F'(u) u' V + ∫ F(u) L V`; then
`∫ F(u) L V = ∫ V L(F∘u)` (symmetry of `L` on test functions) identifies it with
`∫ k (L(ψ_ε∘Γ g) − 2ψ_ε'(Γ g)Γ(g,Lg))`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace
open MarkovTriple.BGL.Compact

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- a compactly supported smooth cut-off of `ψ_ε`. -/
noncomputable def Fcut (ε M : ℝ) (y : ℝ) : ℝ := Real.smoothTransition (2 - y ^ 2 / M ^ 2) * psiS ε y

lemma Fcut_smooth {ε : ℝ} (hε : 0 < ε) (M : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Fcut ε M) :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_id.pow 2).div_const _))).mul
    (psiS_smooth hε)

lemma Fcut_cs (ε : ℝ) {M : ℝ} (hM : 0 < M) : HasCompactSupport (Fcut ε M) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * M)) (b := 2 * M)) fun y hy => ?_
  have : 2 * M < |y| ∨ y < -(2 * M) ∨ 2 * M < y := by
    by_contra h
    push Not at h
    exact hy ⟨by linarith [h.2.1, h.1, abs_nonneg y, neg_abs_le y], by linarith [h.2.2]⟩
  unfold Fcut
  rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
  have h2 : 4 * M ^ 2 ≤ y ^ 2 := by
    rcases this with h | h | h
    · nlinarith [sq_abs y, abs_nonneg y]
    · nlinarith
    · nlinarith
  have hM2 : 0 < M ^ 2 := by positivity
  have : 4 ≤ y ^ 2 / M ^ 2 := by rw [le_div_iff₀ hM2]; linarith
  linarith

lemma Fcut_eq {ε M : ℝ} (hM : 0 < M) {y : ℝ} (hy : |y| ≤ M) : Fcut ε M y = psiS ε y := by
  unfold Fcut
  rw [Real.smoothTransition.one_of_one_le, one_mul]
  have hM2 : 0 < M ^ 2 := by positivity
  have : y ^ 2 / M ^ 2 ≤ 1 := by
    rw [div_le_one hM2]; nlinarith [sq_abs y, abs_nonneg y]
  linarith

lemma Fcut_eventuallyEq {ε M : ℝ} (hM : 0 < M) {y : ℝ} (hy : |y| < M) :
    Fcut ε M =ᶠ[𝓝 y] psiS ε := by
  have : {z : ℝ | |z| < M} ∈ 𝓝 y := (isOpen_lt continuous_abs continuous_const).mem_nhds hy
  filter_upwards [this] with z hz using Fcut_eq hM hz.le

lemma Fcut_zero {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) : Fcut ε M 0 = 0 := by
  rw [Fcut_eq hM (by simpa using hM.le), psiS_zero hε]

namespace CompactTriple

variable (C : CompactTriple E)

/-- constants for the cut-off function `F = Fcut ε (B+1)`. -/
lemma Fcut_bounds {ε : ℝ} (hε : 0 < ε) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K0 K1 K2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ (∀ y, |Fcut ε (B + 1) y| ≤ K0) ∧
      (∀ y, |deriv (Fcut ε (B + 1)) y| ≤ K1) ∧ (∀ y, |deriv (deriv (Fcut ε (B + 1))) y| ≤ K2) :=
  Compact.smooth_bounds (Fcut_smooth hε _) (Fcut_cs ε (by linarith))

lemma J_eq {ε : ℝ} (hε : 0 < ε) (f h : C.A₀) (t : ℝ≥0) {B : ℝ}
    (hB : ∀ r : ℝ, -1 ≤ r → FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r) ≤ᵐ[C.μ] fun _ => B)
    (hB0 : 0 ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    C.toFullTriple.strongPhi ε f h t r =
      ∫ x, Fcut ε (B + 1) ((C.ucls f t r : E → ℝ) x) * (C.orb h r : E → ℝ) x ∂C.μ := by
  unfold FullTriple.strongPhi
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨FullTriple.G C.toFullTriple
      (C.ppt f t r) (C.ppt f t r), C.G_mem₀ (C.ppt_mem f t r) (C.ppt_mem f t r)⟩,
    C.orb_ae h r, hB r (by linarith), C.ΓA_nonneg _ (C.A₀_le _ (C.ppt_mem f t r))] with x a1 a2 a3 a4
  have hFe : Fcut ε (B + 1) ((C.ucls f t r : E → ℝ) x) =
      psiS ε (FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r) x) := by
    unfold ucls; rw [a1]
    have h0 : 0 ≤ FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r) x := a4
    refine Fcut_eq (by linarith) ?_
    rw [abs_of_nonneg h0]; have : FullTriple.G C.toFullTriple (C.ppt f t r) (C.ppt f t r) x ≤ B := a3
    linarith
  rw [hFe, a2, mul_comm]
  rfl

/-- `Γ(g, (-1)•L g) = -Γ(g, L g)`. -/
lemma G_gder (f : C.A₀) (t : ℝ≥0) (s : ℝ) :
    FullTriple.G C.toFullTriple (C.ppt f t s) (C.gder f t s) =ᵐ[C.μ]
      fun x => -FullTriple.G C.toFullTriple (C.ppt f t s) (C.L (C.ppt f t s)) x := by
  have hg : C.ppt f t s ∈ C.A := C.A₀_le _ (C.ppt_mem f t s)
  have hLg : C.L (C.ppt f t s) ∈ C.A := C.A₀_le _ (C.Lm (C.ppt_mem f t s))
  rw [FullTriple.G_comm (C.ppt f t s) (C.gder f t s)]
  unfold gder
  filter_upwards [FullTriple.G_smul_left (T := C.toFullTriple) hLg hg (-1)] with x hx
  rw [hx, FullTriple.G_comm (C.L (C.ppt f t s)) (C.ppt f t s)]; ring

theorem strongInterpolation {ρ : ℝ} {n : ℝ≥0∞} (hCD : C.toFullTriple.CD ρ n) :
    C.toFullTriple.StrongInterpolation where
  continuousOn := by
    intro ε hε f h _ t
    obtain ⟨B, hB0, hB⟩ := C.Gbound hCD f t
    obtain ⟨K0, K1, K2, hK0, hK1, hK2, hb0, hb1, hb2⟩ := Fcut_bounds hε B hB0
    have hFd : Differentiable ℝ (Fcut ε (B + 1)) := (Fcut_smooth hε _).differentiable (by simp)
    have hlip := Compact.lip_of_deriv hFd hb1
    intro r0 hr0
    have hcont : ContinuousAt (fun r => ∫ x, Fcut ε (B + 1) ((C.ucls f t r : E → ℝ) x) *
        (C.orb h r : E → ℝ) x ∂C.μ) r0 :=
      Compact.continuousAt_pair (Fcut_smooth hε _).continuous hb0 hlip
        (C.continuousAt_ucls hCD f t hr0.1) ((C.continuous_orb h).continuousAt)
    exact hcont.continuousWithinAt.congr (fun r hr => C.J_eq hε f h t hB hB0 hr.1)
      (C.J_eq hε f h t hB hB0 hr0.1)
  hasDerivAt := by
    intro ε hε f h _ t s hs
    obtain ⟨B, hB0, hB⟩ := C.Gbound hCD f t
    obtain ⟨K0, K1, K2, hK0, hK1, hK2, hb0, hb1, hb2⟩ := Fcut_bounds hε B hB0
    have hs0 : 0 < s := hs.1
    set F := Fcut ε (B + 1) with hF
    have hFs : ContDiff ℝ (⊤ : ℕ∞) F := Fcut_smooth hε _
    have hFd : Differentiable ℝ F := hFs.differentiable (by simp)
    have hF1s : ContDiff ℝ (⊤ : ℕ∞) (deriv F) := (contDiff_infty_iff_deriv.1 hFs).2
    have hFd2 : Differentiable ℝ (deriv F) := hF1s.differentiable (by simp)
    have htay := Compact.taylor_of_deriv hFd hFd2 hb2
    obtain ⟨M, hM0, hMb⟩ := C.orb_bdd' h
    have hderJ := Compact.hasDerivAt_pair (F := F) (F' := deriv F) hFs.continuous hF1s.continuous
      hb0 hb1 hK2 htay hM0.le hK1 (C.hasDerivAt_ucls hCD f t hs) (C.hasDerivAt_orb h hs0) hMb
    have hev : C.toFullTriple.strongPhi ε f h t =ᶠ[𝓝 s] fun r => ∫ x,
        F ((C.ucls f t r : E → ℝ) x) * (C.orb h r : E → ℝ) x ∂C.μ := by
      filter_upwards [Ioi_mem_nhds hs0] with r hr using C.J_eq hε f h t hB hB0 (le_of_lt hr)
    -- notation
    set g := C.ppt f t s with hg
    set k := C.Pt s.toNNReal h with hk
    have hg0 : g ∈ C.A₀ := C.ppt_mem f t s
    have hk0 : k ∈ C.A₀ := C.Pt_mem _ h
    have hgA : g ∈ C.A := C.A₀_le _ hg0
    have hu : FullTriple.G C.toFullTriple g g ∈ C.A₀ := C.G_mem₀ hg0 hg0
    have huA : FullTriple.G C.toFullTriple g g ∈ C.A := C.A₀_le _ hu
    -- values of `u = Γ g` lie in `[0,B]`
    have hu01 : ∀ᵐ x ∂C.μ, 0 ≤ FullTriple.G C.toFullTriple g g x ∧
        FullTriple.G C.toFullTriple g g x ≤ B := by
      filter_upwards [C.ΓA_nonneg g hgA, hB s (by linarith)] with x h1 h2
      exact ⟨h1, h2⟩
    have hFu_eq : ∀ᵐ x ∂C.μ, F (FullTriple.G C.toFullTriple g g x) =
        psiS ε (FullTriple.G C.toFullTriple g g x) := by
      filter_upwards [hu01] with x hx
      exact Fcut_eq (by linarith) (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
    have hF1_eq : ∀ᵐ x ∂C.μ, deriv F (FullTriple.G C.toFullTriple g g x) =
        deriv (psiS ε) (FullTriple.G C.toFullTriple g g x) := by
      filter_upwards [hu01] with x hx
      exact (Fcut_eventuallyEq (ε := ε) (M := B + 1) (by linarith)
        (by rw [abs_of_nonneg hx.1]; linarith [hx.2])).deriv_eq
    -- the compositions
    have hFuA₀ : (fun x => F (FullTriple.G C.toFullTriple g g x)) ∈ C.A₀ := by
      have := C.toDiffusionTriple.comp_mem 1 (fun z => F (z 0)) (hFs.comp (contDiff_apply ℝ ℝ 0))
        (by simpa using Fcut_zero hε (by linarith : (0 : ℝ) < B + 1))
        ![FullTriple.G C.toFullTriple g g] (by intro i; fin_cases i; simpa using hu)
      simpa using this
    have hFuA : (fun x => F (FullTriple.G C.toFullTriple g g x)) ∈ C.A := C.A₀_le _ hFuA₀
    have hψuA : (fun x => psiS ε (FullTriple.G C.toFullTriple g g x)) ∈ C.A :=
      C.toFullTriple.comp_mem_A (psiS_smooth hε) huA
    have hF1uA : (fun x => deriv F (FullTriple.G C.toFullTriple g g x)) ∈ C.A :=
      C.toFullTriple.comp_mem_A hF1s huA
    have hLFu : C.L (fun x => F (FullTriple.G C.toFullTriple g g x)) =ᵐ[C.μ]
        C.L (fun x => psiS ε (FullTriple.G C.toFullTriple g g x)) :=
      FullTriple.L_congr_A C.toFullTriple hFuA hψuA hFu_eq
    -- integrals
    have hLg : C.L g ∈ C.A₀ := C.Lm hg0
    have hΓgLg : FullTriple.G C.toFullTriple g (C.L g) ∈ C.A₀ :=
      FullTriple.ΓA_mem_A₀ C.toFullTriple hgA hLg
    -- second integral
    have P2 : ∫ x, F ((C.ucls f t s : E → ℝ) x) * (C.orb (C.Lt h) s : E → ℝ) x ∂C.μ =
        ∫ x, k x * C.L (fun y => psiS ε (FullTriple.G C.toFullTriple g g y)) x ∂C.μ := by
      have e1 : ∫ x, F ((C.ucls f t s : E → ℝ) x) * (C.orb (C.Lt h) s : E → ℝ) x ∂C.μ =
          ∫ x, F (FullTriple.G C.toFullTriple g g x) * C.L k x ∂C.μ := by
        refine integral_congr_ae ?_
        filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨FullTriple.G C.toFullTriple g g,
          hu⟩, C.L_Pt h s] with x a1 a2
        have : (C.ucls f t s : E → ℝ) x = FullTriple.G C.toFullTriple g g x := a1
        rw [this, ← a2]
      rw [e1]
      have e2 := C.sym hFuA₀ hk0
      refine (integral_congr_ae (Eventually.of_forall fun x => rfl)).trans ?_
      calc ∫ x, F (FullTriple.G C.toFullTriple g g x) * C.L k x ∂C.μ
          = ∫ x, k x * C.L (fun y => F (FullTriple.G C.toFullTriple g g y)) x ∂C.μ := e2
        _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [hLFu] with x hx
          rw [hx]
    -- first integral
    have P1 : ∫ x, deriv F ((C.ucls f t s : E → ℝ) x) * (C.uder f t s : E → ℝ) x *
        (C.orb h s : E → ℝ) x ∂C.μ =
        ∫ x, k x * (-(2 * deriv (psiS ε) (FullTriple.G C.toFullTriple g g x) *
          FullTriple.G C.toFullTriple g (C.L g) x)) ∂C.μ := by
      refine integral_congr_ae ?_
      filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨FullTriple.G C.toFullTriple g g,
          hu⟩, DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨(2 : ℝ) • FullTriple.G C.toFullTriple g
            (C.gder f t s), C.A₀.smul_mem _ (C.G_mem₀ hg0 (C.gder_mem f t s))⟩, C.orb_ae h s,
        hF1_eq, C.G_gder f t s] with x a1 a2 a3 a4 a5
      have e1 : (C.ucls f t s : E → ℝ) x = FullTriple.G C.toFullTriple g g x := a1
      have e2 : (C.uder f t s : E → ℝ) x = 2 * FullTriple.G C.toFullTriple g (C.gder f t s) x := by
        show (C.toDiffusionTriple.cls ⟨(2 : ℝ) • FullTriple.G C.toFullTriple g (C.gder f t s), _⟩ :
          E → ℝ) x = _
        rw [a2]; simp
      rw [e1, e2, a3, a4, a5]
      show _ = C.Pt s.toNNReal h x * _
      ring
    -- integrability
    have iA : Integrable (fun x => k x * C.L (fun y => psiS ε (FullTriple.G C.toFullTriple g g y)) x)
        C.μ := by
      have := DiffusionTriple.integrable_of_mem C.toDiffusionTriple
        (C.A₀.mul_mem hk0 (C.Lm hFuA₀))
      refine this.congr ?_
      filter_upwards [hLFu] with x hx
      show k x * C.L (fun y => F (FullTriple.G C.toFullTriple g g y)) x = _
      rw [hx]
    have iB : Integrable (fun x => k x * (-(2 * deriv (psiS ε) (FullTriple.G C.toFullTriple g g x) *
        FullTriple.G C.toFullTriple g (C.L g) x))) C.μ := by
      have h1 : (fun x => deriv F (FullTriple.G C.toFullTriple g g x)) ∈ C.A := hF1uA
      have h2 : FullTriple.G C.toFullTriple g (C.L g) * (fun x => deriv F (FullTriple.G C.toFullTriple g g x)) ∈ C.A₀ :=
        C.ideal _ h1 _ hΓgLg
      have h3 : k * ((-2 : ℝ) • (FullTriple.G C.toFullTriple g (C.L g) *
          (fun x => deriv F (FullTriple.G C.toFullTriple g g x)))) ∈ C.A₀ :=
        C.A₀.mul_mem hk0 (C.A₀.smul_mem _ h2)
      have := DiffusionTriple.integrable_of_mem C.toDiffusionTriple h3
      refine this.congr ?_
      filter_upwards [hF1_eq] with x hx
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      rw [hx]; ring
    have iC : Integrable (fun x => k x * psiS ε (FullTriple.G C.toFullTriple g g x)) C.μ := by
      have := DiffusionTriple.integrable_of_mem C.toDiffusionTriple (C.A₀.mul_mem hk0 hFuA₀)
      refine this.congr ?_
      filter_upwards [hFu_eq] with x hx
      simp only [Pi.mul_apply]
      rw [hx]
    have iD : Integrable (fun x => k x * C.toFullTriple.strongD ε g x) C.μ := by
      refine (iA.add iB).congr ?_
      refine Eventually.of_forall fun x => ?_
      simp only [FullTriple.strongD, Pi.add_apply]
      ring
    refine ⟨iC, iD, ?_⟩
    have hD : ∫ x, k x * C.toFullTriple.strongD ε g x ∂C.μ =
        (∫ x, deriv F ((C.ucls f t s : E → ℝ) x) * (C.uder f t s : E → ℝ) x *
          (C.orb h s : E → ℝ) x ∂C.μ) +
        ∫ x, F ((C.ucls f t s : E → ℝ) x) * (C.orb (C.Lt h) s : E → ℝ) x ∂C.μ := by
      rw [P1, P2, ← integral_add iB iA]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [FullTriple.strongD]
      ring
    show HasDerivAt (C.toFullTriple.strongPhi ε f h t)
      (∫ x, k x * C.toFullTriple.strongD ε g x ∂C.μ) s
    rw [hD]
    exact hderJ.congr_of_eventuallyEq hev

end CompactTriple

end MarkovTriple.BGL

/-- **Strong gradient bound on a compact triple** (BGL Thm 3.3.18 for `𝒜 = 𝒜₀`, unconditional):
for `CD(ρ, n)`, `ρ ≥ 0`: `√Γ(P_t f) ≤ e^{-ρt} P_t(√Γ f)` a.e. -/
theorem MarkovTriple.BGL.compact_strong_gradient_bound {E : Type*} [MeasurableSpace E]
    (C : CompactTriple E) {ρ : ℝ} {n : ENNReal} (hCD : C.toFullTriple.CD ρ n) (hρ : 0 ≤ ρ)
    (f : C.A₀) (t : NNReal) :
    ∀ᵐ x ∂C.μ, Real.sqrt (C.toFullTriple.toDiffusionTriple.ΓA (C.Pt t f) (C.Pt t f) x) ≤
      Real.exp (-ρ * t) * (C.toDiffusionTriple.semigroup t (C.toFullTriple.sqrtΓcls f) : Lp ℝ 2 C.μ) x :=
  FullTriple.strong_gradient_bound hCD hρ (C.strongInterpolation hCD) f t
