import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllPI
import MarkovTriple.BGL.Instances.Gibbs.RegSemigroup

/-!
# `WeakHypo` and `F8` for `EllData d` reduce to one elliptic-regularity statement (R16)

`EllData.EllReg` is the classical interior elliptic regularity of the weighted operator `L = w⁻¹ div (w a ∇ ·)`,
in the Sobolev-free form of finite resolvent chains.  It is a **`Prop`** (a named hypothesis of the theorems below,
never an axiom) and is **not proved in this file** (UPDATE round 16: it IS proved for every `EllData d` in `EllRegProof.lean`, `ellReg`) (Mathlib has no Sobolev spaces / elliptic regularity;
see `STATEMENTS_R16_Reg.md`).  Proved:

* `weakHypo_of_reg : E.EllReg → E.WeakHypo` (BGL Def. 3.3.8);
* `f8_of_reg : E.EllReg → E.F8` (BGL Def. 3.3.1 (viii)), via `P_t = R^n ψ_{t,n}(R)` and `resolvent_weak`
  exactly as in `Gibbs/RegSemigroup.lean`;
* `ellReg_of_dim_zero`: `EllReg` holds for `d = 0`; hence `weakHypo`/`f8` unconditional there.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (DiffusionTriple)

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- **Interior elliptic regularity, resolvent-chain form** (Evans §6.3 / Gilbarg–Trudinger Ch. 8 + Sobolev embedding).
For every `m` there is a chain length `n` such that any `L²(μ)` chain `x₀,…,xₙ` with weak equations
`(1 − L) x_k = x_{k+1}` (`k < n`, tested against `C_c^∞`) has a `C^m` representative of `x₀`.
Named hypothesis (a `Prop`) in this file; proved for every `d` in `EllRegProof.lean` (`ellReg`, round 16). -/
def EllReg : Prop :=
  ∀ m : ℕ, ∃ n : ℕ, ∀ x : ℕ → (Rd d → ℝ), (∀ k ≤ n, MemLp (x k) 2 E.μ) →
    (∀ k < n, ∀ a ∈ A₀ d, ∫ y, x k y * E.L a y ∂E.μ = ∫ y, (x k y - x (k + 1) y) * a y ∂E.μ) →
    ∃ g : Rd d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ x 0 =ᵐ[E.μ] g

/-- Two continuous functions equal `μ`-a.e. are equal (`μ` has full support). -/
lemma eq_of_ae_μ {U V : Rd d → ℝ} (hU : Continuous U) (hV : Continuous V) (h : U =ᵐ[E.μ] V) : U = V :=
  (Continuous.ae_eq_iff_eq E.μ hU hV).1 h

/-- Having a `C^m` representative for every `m` gives a `C^∞` one. -/
lemma smooth_rep_of_forall {u : Rd d → ℝ}
    (h : ∀ n : ℕ, ∃ U : Rd d → ℝ, ContDiff ℝ (n : WithTop ℕ∞) U ∧ u =ᵐ[E.μ] U) :
    ∃ U : Rd d → ℝ, Sm U ∧ u =ᵐ[E.μ] U := by
  obtain ⟨U0, hU0, hu0⟩ := h 0
  refine ⟨U0, ?_, hu0⟩
  refine contDiff_infty.2 (fun n => ?_)
  obtain ⟨Un, hUn, hun⟩ := h n
  have : U0 = Un := E.eq_of_ae_μ hU0.continuous hUn.continuous (hu0.symm.trans hun)
  rw [this]; exact hUn

/-- **`WeakHypo` from elliptic regularity** (BGL Def. 3.3.8). -/
theorem weakHypo_of_reg (hR : E.EllReg) : E.WeakHypo := by
  intro l f hweak
  have hm : ∀ m : ℕ, ∃ U : Rd d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) U ∧ (f : Rd d → ℝ) =ᵐ[E.μ] U := by
    intro m
    obtain ⟨n, hn⟩ := hR m
    obtain ⟨g, hg, hae⟩ := hn (fun k => (1 - l) ^ k • (f : Rd d → ℝ))
      (fun k _ => (Lp.memLp f).const_smul _) (by
        intro k _ a ha
        have h1 := hweak ⟨a, ha⟩
        have e1 : ∫ y, ((1 - l) ^ k • (f : Rd d → ℝ)) y * E.L a y ∂E.μ
            = (1 - l) ^ k * ∫ y, (f : Rd d → ℝ) y * E.L a y ∂E.μ := by
          rw [← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp [mul_assoc]
        have e2 : ∫ y, (((1 - l) ^ k • (f : Rd d → ℝ)) y - ((1 - l) ^ (k + 1) • (f : Rd d → ℝ)) y) * a y ∂E.μ
            = (1 - l) ^ k * ∫ y, (l * (f : Rd d → ℝ) y) * a y ∂E.μ := by
          rw [← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [Pi.smul_apply, smul_eq_mul, pow_succ]; ring
        rw [e1, e2]; exact congrArg _ h1)
    refine ⟨g, hg, ?_⟩
    filter_upwards [hae] with y hy
    simpa using hy
  exact E.smooth_rep_of_forall hm

/-- **`F8` from elliptic regularity** (BGL Def. 3.3.1 (viii)). -/
theorem f8_of_reg (hR : E.EllReg) : E.F8 := by
  intro t f
  set S := DiffusionTriple.formData E.diff with hS
  by_cases ht : t = 0
  · subst ht
    refine ⟨f.1, f.2.1, ?_⟩
    have : E.diff.semigroup 0 = 1 := S.semigroup_zero
    rw [this]
    exact E.diff.coeFn_cls f
  · have hmain : ∀ m : ℕ, ∃ X : Rd d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) X ∧
        (E.diff.semigroup t (E.diff.cls f) : Rd d → ℝ) =ᵐ[E.μ] X := by
      intro m
      obtain ⟨n, hn⟩ := hR m
      set Φ : Lp ℝ 2 E.diff.μ := Hilbert.Cx.rcfc (Hilbert.psiFun t n) S.R (E.diff.cls f) with hΦ
      have hP : E.diff.semigroup t = S.R ^ n * Hilbert.Cx.rcfc (Hilbert.psiFun t n) S.R :=
        Hilbert.cfcSemigroup_eq_pow_mul S.R_unitOp ht n
      obtain ⟨g, hg, hae⟩ := hn (fun k => ((S.R ^ (n - k)) Φ : Lp ℝ 2 E.diff.μ))
        (fun k _ => Lp.memLp _) (by
          intro k hk a ha
          have hnk : n - k = (n - k - 1) + 1 := by omega
          have hnk' : n - (k + 1) = n - k - 1 := by omega
          have := E.diff.resolvent_weak ((S.R ^ (n - k - 1)) Φ) a ha
          have e0 : ((S.R ^ (n - k)) Φ : Lp ℝ 2 E.diff.μ) = S.R ((S.R ^ (n - k - 1)) Φ) := by
            rw [hnk, pow_succ']; rfl
          have e1 : ((S.R ^ (n - (k + 1))) Φ : Lp ℝ 2 E.diff.μ) = (S.R ^ (n - k - 1)) Φ := by
            rw [hnk']
          simp only [e0, e1]
          exact this)
      refine ⟨g, hg, ?_⟩
      have e : E.diff.semigroup t (E.diff.cls f) = (S.R ^ n) Φ := by
        rw [hP]; rfl
      have e2 : (E.diff.semigroup t (E.diff.cls f) : Rd d → ℝ) =ᵐ[E.μ] ((S.R ^ (n - 0)) Φ : Rd d → ℝ) := by
        rw [e]; simp
      exact e2.trans hae
    exact E.smooth_rep_of_forall hmain

/-- In dimension `0`, `EllReg` holds (`ℝ^0` is a point; every function is constant). -/
theorem ellReg_of_dim_zero (E : EllData 0) : E.EllReg := by
  intro m
  refine ⟨0, fun x _ _ => ⟨fun _ => x 0 0, contDiff_const, ?_⟩⟩
  refine Eventually.of_forall fun y => ?_
  have : y = 0 := Subsingleton.elim _ _
  subst this; rfl

theorem weakHypo_dim_zero (E : EllData 0) : E.WeakHypo := E.weakHypo_of_reg E.ellReg_of_dim_zero
theorem f8_dim_zero (E : EllData 0) : E.F8 := E.f8_of_reg E.ellReg_of_dim_zero

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
