import MarkovTriple.BGL.Instances.GibbsRd.SobConv
import MarkovTriple.BGL.Instances.GibbsRd.SobOrthant

/-!
# Continuous representative for compactly supported `F` with `HasSobL1 d F` (R16 Sob, S3 core)

`F_n = F ⋆ ρ_n` is uniformly Cauchy: by the Sobolev inequality S1 applied to `F_n − F_m ∈ C_c^∞`,
`‖F_n − F_m‖_∞ ≤ ‖∂_0⋯∂_{d-1}(F_n − F_m)‖_{L¹} = ‖G⋆ρ_n − G⋆ρ_m‖_{L¹} → 0`, where `G` is the iterated weak
derivative `∂_0⋯∂_{d-1} F ∈ L¹` (a.e. supported in the support of `F`).
-/

open MeasureTheory Filter Topology
open scoped ContDiff Convolution Pointwise

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem mol_eq_zero_of_notMem {F ρ : (Fin d → ℝ) → ℝ} {K0 : Set (Fin d → ℝ)} {r : ℝ}
    (hF0 : ∀ᵐ x, x ∉ K0 → F x = 0) (hρ : Function.support ρ ⊆ Metric.ball 0 r) {x : Fin d → ℝ}
    (hx : x ∉ K0 + Metric.closedBall (0 : Fin d → ℝ) r) : mol F ρ x = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hF0] with t ht
  by_cases hρt : ρ (x - t) = 0
  · simp [hρt]
  · by_cases htK : t ∈ K0
    · exfalso
      apply hx
      refine ⟨t, htK, x - t, ?_, by simp⟩
      have := hρ (by simpa using hρt)
      exact mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 this).le
    · simp [ht htK]

theorem hasCompactSupport_mol {F : (Fin d → ℝ) → ℝ} {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0)
    (hF0 : ∀ᵐ x, x ∉ K0 → F x = 0) (n : ℕ) : HasCompactSupport (mol F (rho n)) := by
  refine HasCompactSupport.intro (hK0.add (isCompact_closedBall (0 : Fin d → ℝ) 1)) ?_
  intro x hx
  refine mol_eq_zero_of_notMem (r := 1) hF0 ?_ ?_
  · rw [support_rho]
    refine Metric.ball_subset_ball ?_
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_one this]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · simpa using hx

theorem sob_core {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0) {F : (Fin d → ℝ) → ℝ}
    (hF0 : ∀ᵐ x, x ∉ K0 → F x = 0) (hF : HasSobL1 d F) :
    ∃ g : (Fin d → ℝ) → ℝ, Continuous g ∧ F =ᵐ[volume] g ∧
      TendstoUniformly (fun n => mol F (rho n)) g atTop := by
  have hFloc : LocallyIntegrable F := hF.locallyIntegrable d
  set l : List (Fin d) := List.finRange d with hl
  obtain ⟨G, hW, hG⟩ := exists_weakIter l d (by simp [hl]) hF
  have hGloc : LocallyIntegrable G := HasSobL1.locallyIntegrable _ hG
  have hGae : ∀ᵐ x, x ∈ K0ᶜ → G x = 0 :=
    WeakIter.ae_zero_of_open l hW hK0.isClosed.isOpen_compl (by filter_upwards [hF0] with x hx h using hx h)
  have hGint : Integrable G :=
    (hGloc.integrableOn_isCompact hK0).integrable_of_ae_notMem_eq_zero
      (by filter_upwards [hGae] with x hx h using hx h)
  set Fn : ℕ → (Fin d → ℝ) → ℝ := fun n => mol F (rho n) with hFn
  have hsm : ∀ n, ContDiff ℝ ∞ (Fn n) := fun n =>
    contDiff_mol hFloc (contDiff_rho n) (hasCompactSupport_rho n)
  set c : ℕ → ℝ := fun n => ∫ x, |mol G (rho n) x - G x| with hc
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_integral_abs_mol_sub hGint
  have hcint : ∀ n, Integrable (fun x => |mol G (rho n) x - G x|) := fun n =>
    ((integrable_mol hGint n).sub hGint).abs
  have hbound : ∀ n m x, |Fn n x - Fn m x| ≤ c n + c m := by
    intro n m x
    have hφ : ContDiff ℝ ∞ (fun y => Fn n y - Fn m y) := (hsm n).sub (hsm m)
    have hφc : HasCompactSupport (fun y => Fn n y - Fn m y) :=
      (hasCompactSupport_mol hK0 hF0 n).sub (hasCompactSupport_mol hK0 hF0 m)
    have h1 := abs_le_integral_mixD d _ hφ hφc x
    have h2 : iterD (List.finRange d) (fun y => Fn n y - Fn m y)
        = fun y => mol G (rho n) y - mol G (rho m) y := by
      rw [iterD_sub _ (hsm n) (hsm m)]
      funext y
      simp only [hFn]
      rw [iterD_mol (contDiff_rho n) (hasCompactSupport_rho n) l hW,
        iterD_mol (contDiff_rho m) (hasCompactSupport_rho m) l hW]
    rw [h2] at h1
    refine h1.trans ?_
    calc ∫ y, |mol G (rho n) y - mol G (rho m) y|
        ≤ ∫ y, (|mol G (rho n) y - G y| + |mol G (rho m) y - G y|) := by
          refine integral_mono ?_ ((hcint n).add (hcint m)) fun y => ?_
          · exact ((integrable_mol hGint n).sub (integrable_mol hGint m)).abs
          · calc |mol G (rho n) y - mol G (rho m) y|
                = |(mol G (rho n) y - G y) - (mol G (rho m) y - G y)| := by ring_nf
              _ ≤ _ := abs_sub _ _
      _ = c n + c m := integral_add (hcint n) (hcint m)
  -- pointwise limit
  have hcauchy : ∀ x, ∃ y, Tendsto (fun n => Fn n x) atTop (𝓝 y) := by
    intro x
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have : ∀ᶠ n in atTop, c n < ε / 2 := hc0.eventually (gt_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 this
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have := hbound n N x
    have h1 := hN n hn
    have h2 := hN N le_rfl
    linarith
  choose g hg using hcauchy
  have hunif : ∀ n x, |Fn n x - g x| ≤ c n := by
    intro n x
    have h1 : Tendsto (fun m => |Fn n x - Fn m x|) atTop (𝓝 |Fn n x - g x|) :=
      ((tendsto_const_nhds.sub (hg x)).abs)
    have h2 : Tendsto (fun m => c n + c m) atTop (𝓝 (c n + 0)) :=
      tendsto_const_nhds.add hc0
    have := le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun m => hbound n m x)
    simpa using this
  have hTU : TendstoUniformly Fn g atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hc0.eventually (gt_mem_nhds hε)] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hunif n x) hn
  refine ⟨g, hTU.continuous (Eventually.of_forall fun n => (hsm n).continuous).frequently, ?_, hTU⟩
  filter_upwards [ae_tendsto_mol hFloc] with x hx
  exact tendsto_nhds_unique hx (hg x)

end MarkovTriple.BGL.Instances.GibbsRd.Sob
