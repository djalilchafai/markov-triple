import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.RegLocal
import MarkovTriple.BGL.Instances.Gibbs.RegSemigroup

/-!
# F8 for the zonal Gegenbauer triple: `P_t f ∈ 𝒜` for `f ∈ C_c^∞((-1,1))` (R23-G2)

Same route as `Gibbs/RegSemigroup` (BGL Def. 3.3.1 (viii)): for `t > 0` and every `n`,
`P_t = R^{n+1} ψ_{t,n+1}(R)` (`R` the Friedrichs resolvent), the resolvent identity `∫ (R v) L a = ∫ (R v - v) a`
(`DiffusionTriple.resolvent_weak`) and interior regularity (`go_reg_C1`, `go_reg_gain`, local in `(-1,1)`)
give a representative of `R^{n+1} g` which is `C^{2n+1}` on `(-1,1)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open MarkovTriple.BGL

/-- the Friedrichs resolvent of `goDiff`. -/
noncomputable abbrev goR : Lp ℝ 2 goDiff.μ →L[ℝ] Lp ℝ 2 goDiff.μ :=
  (DiffusionTriple.formData goDiff).R

lemma ae_restrict_of_ae_go {P : ℝ → Prop} (h : ∀ᵐ x ∂goμ, P x) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), P x := by
  have hac : volume.restrict (Ioo (-1 : ℝ) 1) ≪ goμ := by
    refine withDensity_absolutelyContinuous' (f := fun x : ℝ => ENNReal.ofReal (3 / 4 * (1 - x ^ 2)))
      measurable_goρ.aemeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
    have : 0 < 3 / 4 * (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
    exact (ENNReal.ofReal_pos.2 this).ne'
  exact hac.ae_le h

/-- two functions continuous on `(-1,1)` that agree `goμ`-a.e. agree on `(-1,1)`. -/
lemma eqOn_of_ae_go {f g : ℝ → ℝ} (hf : ContinuousOn f (Ioo (-1 : ℝ) 1))
    (hg : ContinuousOn g (Ioo (-1 : ℝ) 1)) (h : ∀ᵐ x ∂goμ, f x = g x) :
    EqOn f g (Ioo (-1 : ℝ) 1) :=
  Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_go h) isOpen_Ioo hf hg

/-- **Resolvent regularity gain**. -/
theorem go_resolvent_gain (v : Lp ℝ 2 goDiff.μ) (j : ℕ)
    (hv : ∃ vt : ℝ → ℝ, ContDiffOn ℝ (j : WithTop ℕ∞) vt (Ioo (-1 : ℝ) 1) ∧
      ∀ᵐ x ∂goμ, (v : ℝ → ℝ) x = vt x) :
    ∃ X : ℝ → ℝ, ContDiffOn ℝ ((j + 2 : ℕ) : WithTop ℕ∞) X (Ioo (-1 : ℝ) 1) ∧
      ∀ᵐ x ∂goμ, (goR v : ℝ → ℝ) x = X x := by
  obtain ⟨vt, hvt, hvae⟩ := hv
  have hx : Integrable (goR v : ℝ → ℝ) goμ := (Lp.memLp _).integrable (by norm_num)
  have hvi : Integrable (v : ℝ → ℝ) goμ := (Lp.memLp _).integrable (by norm_num)
  have hh : Integrable (fun y => (goR v : ℝ → ℝ) y - (v : ℝ → ℝ) y) goμ := hx.sub hvi
  have hweak : ∀ a ∈ goA₀, ∫ y, (goR v : ℝ → ℝ) y * goL a y ∂goμ =
      ∫ y, ((fun y => (goR v : ℝ → ℝ) y - (v : ℝ → ℝ) y) y) * a y ∂goμ :=
    fun a ha => DiffusionTriple.resolvent_weak goDiff v a ha
  have key : ∀ i : ℕ, i ≤ j + 2 →
      ∃ X : ℝ → ℝ, ContDiffOn ℝ (i : WithTop ℕ∞) X (Ioo (-1 : ℝ) 1) ∧
        ∀ᵐ x ∂goμ, (goR v : ℝ → ℝ) x = X x := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨U, c, hU, hae, -⟩ := go_reg_C1 hx hh hweak
      exact ⟨U, hU.of_le (by norm_num), hae⟩
    | succ i ih =>
      intro hi
      obtain ⟨X, hX, hXae⟩ := ih (by omega)
      set k : ℕ := min i j with hk
      have hXk : ContDiffOn ℝ (k : WithTop ℕ∞) X (Ioo (-1 : ℝ) 1) :=
        hX.of_le (by exact_mod_cast min_le_left i j)
      have hvk : ContDiffOn ℝ (k : WithTop ℕ∞) vt (Ioo (-1 : ℝ) 1) :=
        hvt.of_le (by exact_mod_cast min_le_right i j)
      obtain ⟨U, hU, hUae⟩ := go_reg_gain (ht := fun y => X y - vt y) k hx hh hweak
        (hXk.sub hvk) (by
          filter_upwards [hXae, hvae] with y h1 h2
          simp only [h1, h2])
      refine ⟨U, hU.of_le ?_, hUae⟩
      have : i + 1 ≤ k + 2 := by omega
      have h2 : ((i + 1 : ℕ) : WithTop ℕ∞) ≤ ((k + 2 : ℕ) : WithTop ℕ∞) := by exact_mod_cast this
      push_cast at h2 ⊢
      exact h2
  exact key (j + 2) le_rfl

/-- `R^{m+1} g ∈ C^{2m+1}((-1,1))` for every `g ∈ L²(μ)`. -/
theorem go_resolvent_pow_reg (m : ℕ) (g : Lp ℝ 2 goDiff.μ) :
    ∃ X : ℝ → ℝ, ContDiffOn ℝ ((2 * m + 1 : ℕ) : WithTop ℕ∞) X (Ioo (-1 : ℝ) 1) ∧
      ∀ᵐ x ∂goμ, ((goR ^ (m + 1)) g : ℝ → ℝ) x = X x := by
  induction m with
  | zero =>
    have hx : Integrable (goR g : ℝ → ℝ) goμ := (Lp.memLp _).integrable (by norm_num)
    have hvi : Integrable (g : ℝ → ℝ) goμ := (Lp.memLp _).integrable (by norm_num)
    obtain ⟨U, c, hU, hae, -⟩ := go_reg_C1 hx (hx.sub hvi)
      (fun a ha => DiffusionTriple.resolvent_weak goDiff g a ha)
    exact ⟨U, by simpa using hU, by simpa using hae⟩
  | succ m ih =>
    obtain ⟨X, hX, hae⟩ := ih
    obtain ⟨Y, hY, haeY⟩ := go_resolvent_gain ((goR ^ (m + 1)) g) (2 * m + 1) ⟨X, hX, hae⟩
    refine ⟨Y, ?_, ?_⟩
    · have : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by ring
      rw [this]; exact hY
    · rw [pow_succ']
      exact haeY

/-- a function with `C^n((-1,1))` representatives (`goμ`-a.e.) for every `n` has a representative in `𝒜`. -/
lemma exists_goA_rep {u : ℝ → ℝ}
    (h : ∀ n : ℕ, ∃ U : ℝ → ℝ, ContDiffOn ℝ (n : WithTop ℕ∞) U (Ioo (-1 : ℝ) 1) ∧
      ∀ᵐ x ∂goμ, u x = U x) : ∃ g ∈ goA, u =ᵐ[goμ] g := by
  classical
  obtain ⟨U0, hU0, hu0⟩ := h 0
  have hsm : ∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) U0 (Ioo (-1 : ℝ) 1) := by
    intro n
    obtain ⟨Un, hUn, hun⟩ := h n
    have heq : EqOn U0 Un (Ioo (-1 : ℝ) 1) := eqOn_of_ae_go
      (hU0.continuousOn) (hUn.continuousOn) (by
        filter_upwards [hu0, hun] with x h1 h2
        rw [← h1, ← h2])
    exact hUn.congr (fun x hx => heq hx)
  set g : ℝ → ℝ := (Ioo (-1 : ℝ) 1).piecewise U0 (fun _ => 0) with hg
  have hgU : ∀ x ∈ Ioo (-1 : ℝ) 1, g x = U0 x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · exact (hU0.continuousOn).measurable_piecewise continuousOn_const measurableSet_Ioo
  · exact contDiffOn_infty.2 fun n => (hsm n).congr hgU
  · filter_upwards [hu0, ae_go (p := fun x => x ∈ Ioo (-1 : ℝ) 1) fun x hx => hx] with x h1 h2
    rw [h1, hgU x h2]

/-- **F8 for `goDiff`**: `P_t f ∈ 𝒜` for `f ∈ 𝒜₀`. -/
theorem go_F8 (t : ℝ≥0) (f : goDiff.A₀) :
    ∃ g ∈ goA, (goDiff.semigroup t (goDiff.cls f) : ℝ → ℝ) =ᵐ[goμ] g := by
  set S := DiffusionTriple.formData goDiff with hS
  by_cases ht : t = 0
  · subst ht
    refine ⟨f.1, goA₀_le_goA f.2, ?_⟩
    have : goDiff.semigroup 0 = 1 := S.semigroup_zero
    rw [this]
    exact DiffusionTriple.coeFn_cls goDiff f
  · refine exists_goA_rep fun n => ?_
    have hP : goDiff.semigroup t =
        S.R ^ (n + 1) * Hilbert.Cx.rcfc (Hilbert.psiFun t (n + 1)) S.R :=
      Hilbert.cfcSemigroup_eq_pow_mul S.R_unitOp ht (n + 1)
    obtain ⟨X, hX, hae⟩ := go_resolvent_pow_reg n
      (Hilbert.Cx.rcfc (Hilbert.psiFun t (n + 1)) S.R (goDiff.cls f))
    refine ⟨X, hX.of_le ?_, ?_⟩
    · have : n ≤ 2 * n + 1 := by omega
      exact_mod_cast this
    · rw [hP]; exact hae

end MarkovTriple.BGL.Instances.GegenbauerOpen
