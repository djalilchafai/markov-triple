import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.PreFull
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Sem
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Ergodic
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Curv
import MarkovTriple.BGL.Instances.GegenbauerOpen.NotComplete
import MarkovTriple.BGL.Theory.ESAOne
import MarkovTriple.BGL.Frozen.CD

/-!
# The zonal Gegenbauer `FullTriple` over `(-1,1)` with `𝒜₀ = C_c^∞((-1,1))`, conditionally on F10 (R23-G2)

`goFull hF10 : FullTriple ℝ` with underlying diffusion triple `goDiff`, `𝒜 = goA`
(measurable, `C^∞` on `(-1,1)`).  Every field is proved except F10 (`esa`), which is the hypothesis
`hF10 : goDiff.ESAProp`.  Uses of `hF10`: the field `esa` itself, and S11 (`conservative`, through
`DiffusionTriple.conservative_of_esa`).  S10 (ergodicity), F8 and F1-F7, F9 do not use it.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open MarkovTriple.BGL

/-- The Standard Markov Triple over `goDiff` (S10 proved; S11 from F10). -/
noncomputable def goStandard (hF10 : goDiff.ESAProp) : StandardTriple ℝ where
  toDiffusionTriple := goDiff
  ergodic := go_ergodic
  conservative := fun _ hu _ t =>
    DiffusionTriple.conservative_of_esa (T := goDiff) hF10 hu t

/-- **The Full Markov Triple over `goDiff`**, conditionally on F10. -/
noncomputable def goFull (hF10 : goDiff.ESAProp) : FullTriple ℝ where
  toStandardTriple := goStandard hF10
  A := goA
  A₀_le := goPreFull.A₀_le
  A_measurable := goPreFull.A_measurable
  ideal := goPreFull.ideal
  pos_detect := goPreFull.pos_detect
  A_comp := fun k ψ hψ f hf => go_A_comp k ψ hψ f hf
  L_mem_A := goPreFull.L_mem_A
  ΓA_nonneg := goPreFull.ΓA_nonneg
  diffusion_Γ_A := goPreFull.diffusion_Γ_A
  diffusion_L_A := fun k ψ hψ f hf => go_diffusion_L_A k ψ hψ f hf
  ibp_A := goPreFull.ibp_A
  semigroup_A := go_F8
  connected := goPreFull.connected
  esa := hF10

theorem goFull_toDiffusionTriple (hF10 : goDiff.ESAProp) :
    (goFull hF10).toDiffusionTriple = goDiff := rfl

/-- **`CD(ρ,n)` for `goFull`** (`ρ ≤ 3`, `n ≥ 4`), in the library's `FullTriple.CD`. -/
theorem goFull_CD' (hF10 : goDiff.ESAProp) {ρ : ℝ} {n : ℝ≥0∞} (hρ : ρ ≤ 3) (hn : 4 ≤ n) :
    (goFull hF10).CD ρ n :=
  ⟨le_trans (by norm_num) hn, fun f hf =>
    ae_go fun x hx => goA_CD hρ hn hf x hx⟩

/-- **`CD(3,4) = CD(n-1,n)` for `n = 4`**. -/
theorem goFull_CD (hF10 : goDiff.ESAProp) : (goFull hF10).CD 3 4 :=
  goFull_CD' hF10 le_rfl le_rfl

/-- **`goFull` is not complete** (BGL Def. 3.3.9). -/
theorem goFull_not_complete (hF10 : goDiff.ESAProp) :
    ¬ (goFull hF10).toDiffusionTriple.IsComplete :=
  go_not_complete

end MarkovTriple.BGL.Instances.GegenbauerOpen
