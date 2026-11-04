import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllRegProof
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdResolvent

/-!
# `Core2` for `EllData d`: pointwise `L, Γ, Γ₂` calculus (R19, Stream A6)

Statements: `STATEMENTS_R19_Core2Ell.md` (C0, C1).  Everything is stated for a general `E : EllData d` and in the
`L, Γ, Γ₂` calculus (no coordinates of `a` or `w`): Cauchy–Schwarz for `Γ`, linearity of `L`, `Γ`, `Γ₂` on `C^∞`,
Cauchy–Schwarz for `Γ₂ - ρΓ` under `Curv ρ`, locality (cut-offs equal to `1` near a point), and the cut-off
hypothesis class `CutFamily` / `CoreCut`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

/-- a real quadratic polynomial that is nonnegative has nonpositive discriminant: `B² ≤ A C`. -/
lemma cs_of_nonneg_quad {A B C : ℝ} (h : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C) : B ^ 2 ≤ A * C := by
  have := discrim_le_zero (a := C) (b := 2 * B) (c := A) (fun t => by
    have := h t; nlinarith)
  unfold discrim at this
  nlinarith

namespace EllData
variable (E : EllData d)

/-- `Γ₂(f,g) = ½(L Γ(f,g) - Γ(Lf,g) - Γ(f,Lg))` (BGL Def. 3.3.12, polarised). **C0**. -/
noncomputable def G2 (f g : Rd d → ℝ) (x : Rd d) : ℝ :=
  (E.L (E.Γ f g) x - E.Γ (E.L f) g x - E.Γ f (E.L g) x) / 2

/-- the bilinear form `Q_x(u,w) = Σ aᵢⱼ(x) uᵢ wⱼ`. -/
noncomputable def Qcm (x : Rd d) (u w : Fin d → ℝ) : ℝ := ∑ i, ∑ j, E.a i j x * u i * w j

lemma Γ_eq_Qcm (f g : Rd d → ℝ) (x : Rd d) :
    E.Γ f g x = E.Qcm x (fun i => pderiv f i x) (fun j => pderiv g j x) := rfl

lemma Qcm_nonneg (x : Rd d) (u : Fin d → ℝ) : 0 ≤ E.Qcm x u u := by
  by_cases h : u = 0
  · subst h; simp [Qcm]
  · exact (E.a_pos x u h).le

lemma Qcm_add_smul (x : Rd d) (u w : Fin d → ℝ) (t : ℝ) :
    E.Qcm x (fun i => u i + t * w i) (fun i => u i + t * w i) =
      E.Qcm x u u + 2 * t * E.Qcm x u w + t ^ 2 * E.Qcm x w w := by
  have hs : E.Qcm x w u = E.Qcm x u w := by
    unfold Qcm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [E.a_symm j i x]; ring
  have h1 : E.Qcm x (fun i => u i + t * w i) (fun i => u i + t * w i) =
      E.Qcm x u u + t * E.Qcm x u w + t * E.Qcm x w u + t ^ 2 * E.Qcm x w w := by
    unfold Qcm
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, hs]; ring

/-- Cauchy–Schwarz for `Q_x`. -/
lemma Qcm_cs (x : Rd d) (u w : Fin d → ℝ) : (E.Qcm x u w) ^ 2 ≤ (E.Qcm x u u) * (E.Qcm x w w) := by
  refine cs_of_nonneg_quad fun t => ?_
  rw [← E.Qcm_add_smul]
  exact E.Qcm_nonneg x _

/-- **Cauchy–Schwarz for `Γ`**: `Γ(f,g)² ≤ Γ(f)Γ(g)`. -/
lemma Γ_cs (f g : Rd d → ℝ) (x : Rd d) : E.Γ f g x ^ 2 ≤ E.Γ f f x * E.Γ g g x :=
  E.Qcm_cs x _ _

lemma Γ_symm_apply (f g : Rd d → ℝ) (x : Rd d) : E.Γ f g x = E.Γ g f x := congrFun (E.Γ_symm f g) x

/-- `Γ(f + c g, k) = Γ(f,k) + c Γ(g,k)` -/
lemma Γ_lin_left {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (c : ℝ) (k : Rd d → ℝ) :
    E.Γ (fun y => f y + c * g y) k = fun y => E.Γ f k y + c * E.Γ g k y := by
  funext y
  have h1 : ∀ i, pderiv (fun y => f y + c * g y) i y = pderiv f i y + c * pderiv g i y := by
    intro i
    rw [pderiv_add' hf (contDiff_const.mul hg) i y, pderiv_mul' contDiff_const hg i y, pderiv_const]
    ring
  simp only [Γ, h1, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma Γ_lin_right {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (c : ℝ) (k : Rd d → ℝ) :
    E.Γ k (fun y => f y + c * g y) = fun y => E.Γ k f y + c * E.Γ k g y := by
  rw [E.Γ_symm, E.Γ_lin_left hf hg c k]
  funext y
  rw [E.Γ_symm_apply f k y, E.Γ_symm_apply g k y]

lemma Γ_quad {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (t : ℝ) (x : Rd d) :
    E.Γ (fun y => f y + t * g y) (fun y => f y + t * g y) x =
      E.Γ f f x + 2 * t * E.Γ f g x + t ^ 2 * E.Γ g g x := by
  have h1 := congrFun (E.Γ_lin_left hf hg t (fun y => f y + t * g y)) x
  have h2 := congrFun (E.Γ_lin_right hf hg t f) x
  have h3 := congrFun (E.Γ_lin_right hf hg t g) x
  rw [h1]
  rw [h2, h3, E.Γ_symm_apply g f x]
  ring

/-- `Γ(f - g) ≤ 2Γ(f) + 2Γ(g)`. -/
lemma Γ_sub_le {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (x : Rd d) :
    E.Γ (fun y => f y + (-1 : ℝ) * g y) (fun y => f y + (-1 : ℝ) * g y) x ≤
      2 * E.Γ f f x + 2 * E.Γ g g x := by
  have h1 := E.Γ_quad hf hg (-1) x
  have h2 := E.Γ_quad hf hg 1 x
  have h3 := E.Γ_nonneg (fun y => f y + (1 : ℝ) * g y) x
  rw [h2] at h3
  rw [h1]
  nlinarith

/-! ### locality -/

lemma pderiv_congr_loc {f g : Rd d → ℝ} {x : Rd d} (h : f =ᶠ[𝓝 x] g) (i : Fin d) :
    pderiv f i x = pderiv g i x := by
  unfold pderiv
  rw [h.fderiv_eq]

lemma pderiv_eventuallyEq {f g : Rd d → ℝ} {x : Rd d} (h : f =ᶠ[𝓝 x] g) (i : Fin d) :
    pderiv f i =ᶠ[𝓝 x] pderiv g i := by
  filter_upwards [h.eventually_nhds] with y hy
  exact pderiv_congr_loc hy i

lemma Γ_congr_loc {f f' g g' : Rd d → ℝ} {x : Rd d} (hf : f =ᶠ[𝓝 x] f') (hg : g =ᶠ[𝓝 x] g') :
    E.Γ f g x = E.Γ f' g' x := by
  simp only [Γ, pderiv_congr_loc hf, pderiv_congr_loc hg]

lemma L_congr_loc {f g : Rd d → ℝ} {x : Rd d} (h : f =ᶠ[𝓝 x] g) : E.L f x = E.L g x := by
  unfold L
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine pderiv_congr_loc ?_ i
  filter_upwards [h.eventually_nhds] with y hy
  simp only [pderiv_congr_loc hy]

lemma L_const (c : ℝ) (x : Rd d) : E.L (fun _ => c) x = 0 := by
  unfold L
  simp only [pderiv_const, mul_zero, Finset.sum_const_zero]

/-- if `F = 1` near `x`, all the cut-off jets vanish at `x`. -/
lemma loc_one {F : Rd d → ℝ} {x : Rd d} (hF : ∀ᶠ y in 𝓝 x, F y = 1) :
    (∀ k, E.Γ F k x = 0) ∧ E.L F x = 0 ∧ E.L (E.L F) x = 0 ∧ (∀ k, E.Γ (E.L F) k x = 0) ∧
      (∀ k, E.G2 F k x = 0) := by
  have hΓ : ∀ {y : Rd d}, (∀ᶠ z in 𝓝 y, F z = 1) → ∀ k, E.Γ F k y = 0 := by
    intro y hy k
    simp only [Γ, pderiv_congr_loc (show F =ᶠ[𝓝 y] fun _ => (1 : ℝ) from hy), pderiv_const]
    simp
  have hL : ∀ {y : Rd d}, (∀ᶠ z in 𝓝 y, F z = 1) → E.L F y = 0 := by
    intro y hy
    rw [E.L_congr_loc (show F =ᶠ[𝓝 y] fun _ => (1 : ℝ) from hy)]
    exact E.L_const 1 y
  have hLev : E.L F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hF.eventually_nhds] with y hy
    exact hL hy
  have hΓev : ∀ k, E.Γ F k =ᶠ[𝓝 x] fun _ => (0 : ℝ) := fun k => by
    filter_upwards [hF.eventually_nhds] with y hy
    exact hΓ hy k
  have hLL : E.L (E.L F) x = 0 := by
    rw [E.L_congr_loc hLev]; exact E.L_const 0 x
  have hΓL : ∀ k, E.Γ (E.L F) k x = 0 := fun k => by
    rw [E.Γ_congr_loc hLev (Filter.EventuallyEq.refl _ k)]
    simp [Γ, pderiv_const]
  refine ⟨hΓ hF, hL hF, hLL, hΓL, fun k => ?_⟩
  unfold G2
  rw [E.L_congr_loc (hΓev k), E.L_const, hΓL k, hΓ hF (E.L k)]
  ring

/-! ### linearity of `L` and `Γ₂` -/

lemma P_lin {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (c : ℝ) (i : Fin d) :
    E.P (fun y => f y + c * g y) i = fun y => E.P f i y + c * E.P g i y := by
  funext y
  have h1 : ∀ j, pderiv (fun y => f y + c * g y) j y = pderiv f j y + c * pderiv g j y := by
    intro j
    rw [pderiv_add' hf (contDiff_const.mul hg) j y, pderiv_mul' contDiff_const hg j y, pderiv_const]
    ring
  have hs : ∑ j, E.a i j y * (pderiv f j y + c * pderiv g j y) =
      ∑ j, E.a i j y * pderiv f j y + c * ∑ j, E.a i j y * pderiv g j y := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [P, h1, hs]
  ring

/-- `L(f + c g) = Lf + c Lg`. -/
lemma L_lin {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (c : ℝ) :
    E.L (fun y => f y + c * g y) = fun y => E.L f y + c * E.L g y := by
  funext x
  have h2 : ∀ i, pderiv (E.P (fun y => f y + c * g y) i) i x =
      pderiv (E.P f i) i x + c * pderiv (E.P g i) i x := by
    intro i
    rw [E.P_lin hf hg c i, pderiv_add' (E.sm_P hf i) (contDiff_const.mul (E.sm_P hg i)) i x,
      pderiv_mul' contDiff_const (E.sm_P hg i) i x, pderiv_const]
    ring
  show E.L (fun y => f y + c * g y) x = E.L f x + c * E.L g x
  rw [E.L_eq, E.L_eq f, E.L_eq g]
  simp only [h2]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

lemma G2_symm (f g : Rd d → ℝ) (x : Rd d) : E.G2 f g x = E.G2 g f x := by
  unfold G2
  rw [E.Γ_symm f g, E.Γ_symm_apply (E.L f) g x, E.Γ_symm_apply f (E.L g) x]
  ring

lemma G2_lin_left {f g k : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (hk : Sm k) (c : ℝ) (x : Rd d) :
    E.G2 (fun y => f y + c * g y) k x = E.G2 f k x + c * E.G2 g k x := by
  unfold G2
  have e1 := congrFun (E.Γ_lin_left hf hg c k)
  have e2 := congrFun (E.L_lin hf hg c)
  have hs1 : Sm (fun y => E.L f y) := E.sm_L hf
  have hs2 : Sm (fun y => E.L g y) := E.sm_L hg
  have e3 := congrFun (E.Γ_lin_left hs1 hs2 c k)
  have e4 := congrFun (E.Γ_lin_left hf hg c (E.L k))
  have hL1 : E.L (E.Γ (fun y => f y + c * g y) k) x = E.L (fun y => E.Γ f k y + c * E.Γ g k y) x := by
    rw [E.Γ_lin_left hf hg c k]
  rw [hL1, congrFun (E.L_lin (E.sm_Γ hf hk) (E.sm_Γ hg hk) c) x]
  have hL2 : E.Γ (E.L (fun y => f y + c * g y)) k x =
      E.Γ (fun y => E.L f y + c * E.L g y) k x := by
    rw [E.L_lin hf hg c]
  rw [hL2, e3 x, e4 x]
  ring

lemma G2_quad {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (t : ℝ) (x : Rd d) :
    E.G2 (fun y => f y + t * g y) (fun y => f y + t * g y) x =
      E.G2 f f x + 2 * t * E.G2 f g x + t ^ 2 * E.G2 g g x := by
  have hh : Sm (fun y => f y + t * g y) := hf.add (contDiff_const.mul hg)
  rw [E.G2_symm _ (fun y => f y + t * g y), E.G2_lin_left hf hg hh t x]
  rw [E.G2_symm f (fun y => f y + t * g y), E.G2_symm g (fun y => f y + t * g y),
    E.G2_lin_left hf hg hf t x, E.G2_lin_left hf hg hg t x, E.G2_symm g f x]
  ring

/-- `Curv ρ` pointwise: `ρ Γ(f) ≤ Γ₂(f)` for the formula `G2`. -/
lemma curv_G2 {ρ : ℝ} (hρ : E.Curv ρ) {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) :
    ρ * E.Γ f f x ≤ E.G2 f f x := by
  have h := hρ f hf x
  rw [E.ΓA_eq hf hf, E.Γ₂_eq_comb hf] at h
  have h' : ρ * E.Γ f f x ≤ (E.L (E.Γ f f) x - E.Γ f (E.L f) x - E.Γ (E.L f) f x) / 2 := h
  unfold G2
  linarith [E.Γ_symm_apply (E.L f) f x]

/-- `Γ₂'(f,g) = Γ₂(f,g) - ρ Γ(f,g)`. -/
noncomputable def G2' (ρ : ℝ) (f g : Rd d → ℝ) (x : Rd d) : ℝ := E.G2 f g x - ρ * E.Γ f g x

/-- **Cauchy–Schwarz for `Γ₂ - ρΓ`** (a nonnegative symmetric bilinear form on `C^∞` under `Curv ρ`). -/
lemma G2'_cs {ρ : ℝ} (hρ : E.Curv ρ) {f g : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (x : Rd d) :
    E.G2' ρ f g x ^ 2 ≤ E.G2' ρ f f x * E.G2' ρ g g x := by
  refine cs_of_nonneg_quad fun t => ?_
  have h := E.curv_G2 hρ (hf.add (contDiff_const.mul hg) : Sm (fun y => f y + t * g y)) x
  rw [E.G2_quad hf hg t x, E.Γ_quad hf hg t x] at h
  unfold G2'
  nlinarith

lemma G2'_nonneg {ρ : ℝ} (hρ : E.Curv ρ) {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) : 0 ≤ E.G2' ρ f f x := by
  have := E.curv_G2 hρ hf x
  unfold G2'; linarith

/-! ### Leibniz expansions for the cut-off commutators -/

lemma sm_G2_aux {f : Rd d → ℝ} (hf : Sm f) : Sm (E.L f) := E.sm_L hf

/-- `L(F v) = F Lv + v LF + 2Γ(F,v)`. -/
lemma L_cut {F v : Rd d → ℝ} (hF : Sm F) (hv : Sm v) (x : Rd d) :
    E.L (F * v) x = F x * E.L v x + v x * E.L F x + 2 * E.Γ F v x := by
  exact E.L_mul hF hv x

/-- `LL(F v) = F LLv + 2 LF·Lv + 4Γ(F,Lv) + v LLF + 4Γ(LF,v) + 4Γ₂(F,v)`. -/
lemma LL_cut {F v : Rd d → ℝ} (hF : Sm F) (hv : Sm v) (x : Rd d) :
    E.L (E.L (F * v)) x = F x * E.L (E.L v) x + 2 * (E.L F x * E.L v x) + 4 * E.Γ F (E.L v) x +
      v x * E.L (E.L F) x + 4 * E.Γ (E.L F) v x + 4 * E.G2 F v x := by
  have hLv := E.sm_L hv
  have hLF := E.sm_L hF
  have e1 : E.L (F * v) = fun y => F y * E.L v y + 1 * (v y * E.L F y + 2 * E.Γ F v y) := by
    funext y; rw [E.L_cut hF hv y]; ring
  have hs1 : Sm (fun y => F y * E.L v y) := hF.mul hLv
  have hs2 : Sm (fun y => v y * E.L F y + 2 * E.Γ F v y) :=
    (hv.mul hLF).add (contDiff_const.mul (E.sm_Γ hF hv))
  rw [e1, congrFun (E.L_lin hs1 hs2 1) x]
  have h1 : E.L (fun y => F y * E.L v y) x = F x * E.L (E.L v) x + E.L v x * E.L F x +
      2 * E.Γ F (E.L v) x := E.L_mul hF hLv x
  have h2 : E.L (fun y => v y * E.L F y + 2 * E.Γ F v y) x =
      E.L (fun y => v y * E.L F y) x + 2 * E.L (E.Γ F v) x := by
    have := congrFun (E.L_lin (f := fun y => v y * E.L F y) (g := E.Γ F v) (hv.mul hLF)
      (E.sm_Γ hF hv) 2) x
    simpa using this
  have h3 : E.L (fun y => v y * E.L F y) x = v x * E.L (E.L F) x + E.L F x * E.L v x +
      2 * E.Γ v (E.L F) x := E.L_mul hv hLF x
  rw [h1, h2, h3]
  unfold G2
  rw [E.Γ_symm_apply v (E.L F) x]
  ring

/-! ### the hypothesis class `H` -/

/-- **C1**: a cut-off family: smooth, compactly supported, `0 ≤ χ_n ≤ 1`, eventually `≡ 1` near every point, with
uniformly bounded `Γ(χ_n)`, `Lχ_n`, `L²χ_n`, `Γ(Lχ_n)` and `Γ₂(χ_n)`. -/
structure CutFamily (E : EllData d) (χ : ℕ → Rd d → ℝ) : Prop where
  smooth : ∀ n, Sm (χ n)
  cs : ∀ n, HasCompactSupport (χ n)
  mem : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1
  eventually_one : ∀ x, ∀ᶠ n in atTop, ∀ᶠ y in 𝓝 x, χ n y = 1
  bound : ∃ K : ℝ, ∀ n x, E.Γ (χ n) (χ n) x ≤ K ∧ |E.L (χ n) x| ≤ K ∧ |E.L (E.L (χ n)) x| ≤ K ∧
    E.Γ (E.L (χ n)) (E.L (χ n)) x ≤ K ∧ E.G2 (χ n) (χ n) x ≤ K

/-- **C1**: `E` admits a cut-off family (hypothesis class `H`). -/
def CoreCut (E : EllData d) : Prop := ∃ χ : ℕ → Rd d → ℝ, E.CutFamily χ

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
