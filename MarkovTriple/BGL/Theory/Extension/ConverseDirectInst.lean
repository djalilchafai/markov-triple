import Mathlib
import MarkovTriple.BGL.Theory.Extension.ConverseDirect
import MarkovTriple.BGL.Theory.Complete.Instances
import MarkovTriple.BGL.Instances.OU.Core2
import MarkovTriple.BGL.Instances.Circle.Triple
import MarkovTriple.BGL.Theory.Conservation.Compact
import MarkovTriple.BGL.Instances.Lebesgue.Core2
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllMain
import MarkovTriple.BGL.Instances.Riemannian.Core2RiemMain

/-!
# Non-vacuity of `FullTriple.mem_domain_of_Γ₂_direct` (Round 20, Stream D3)

## DIFFERENCE FROM BGL

BGL's converse (Prop. 3.3.17, p. 162) uses the `L²`-core step (`FullTriple.Core2`, ERRATA R15-1).  The theorem
applied here (`FullTriple.mem_domain_of_Γ₂_direct`) does NOT: it uses completeness (Def. 3.3.9) + ESA + `CD(ρ,n)` and
the cut-off identity of BGL Prop. 3.2.1 applied to `Γ₂`.  Below it is applied to three concrete `FullTriple`s without
mentioning `Core2`: OU (`CD(1,∞)`, non-compact, `𝒜 ≠ 𝒜₀`), the circle, and Lebesgue on `ℝ` (`CD(0,∞)`).
For OU the result is compared with the `Core2`-based `ou_mem_domain_of_Γ₂`.
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances

open MarkovTriple.Sanity.Circle

/-- OU, direct converse (compare `OU.ou_mem_domain_of_Γ₂`, which goes through `Core2` and the Hermite density). -/
theorem OU.ou_mem_domain_of_Γ₂_direct {f : ℝ → ℝ} (hf : f ∈ OU.ouFull.A) (hf2 : MemLp f 2 OU.ouFull.μ)
    (hG : Integrable (FullTriple.G OU.ouFull f f) OU.ouFull.μ)
    (hG2 : Integrable (OU.ouFull.toDiffusionTriple.Γ₂ f f) OU.ouFull.μ) :
    ∃ hF : hf2.toLp f ∈ OU.ouFull.toDiffusionTriple.generator.domain,
      ((OU.ouFull.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 OU.ouFull.μ) : ℝ → ℝ) =ᵐ[OU.ouFull.μ]
        OU.ouFull.L f :=
  FullTriple.mem_domain_of_Γ₂_direct ouDiff_isComplete OU.ouFull_CD hf hf2 hG hG2

/-- Circle (compact, `𝒜 = 𝒜₀`), `CD(0,∞)`: completeness comes from compactness. -/
theorem circle_mem_domain_of_Γ₂_direct {f : 𝕋 → ℝ} (hf : f ∈ Circle.circleCompact.toFullTriple.A)
    (hf2 : MemLp f 2 Circle.circleCompact.toFullTriple.μ)
    (hG : Integrable (FullTriple.G Circle.circleCompact.toFullTriple f f) Circle.circleCompact.toFullTriple.μ)
    (hG2 : Integrable (Circle.circleCompact.toFullTriple.toDiffusionTriple.Γ₂ f f)
      Circle.circleCompact.toFullTriple.μ) :
    ∃ hF : hf2.toLp f ∈ Circle.circleCompact.toFullTriple.toDiffusionTriple.generator.domain,
      ((Circle.circleCompact.toFullTriple.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 Circle.circleCompact.toFullTriple.μ) : 𝕋 → ℝ) =ᵐ[Circle.circleCompact.toFullTriple.μ]
        Circle.circleCompact.toFullTriple.L f :=
  FullTriple.mem_domain_of_Γ₂_direct (CompactTriple.isComplete Circle.circleCompact)
    Circle.circle_CD_zero_top hf hf2 hG hG2

/-- Lebesgue on `ℝ` (infinite measure, `𝒜₀ = C_c^∞`), `CD(0,∞)`. -/
theorem lebesgue_mem_domain_of_Γ₂_direct {f : ℝ → ℝ} (hf : f ∈ Lebesgue.lebesgueFull.A)
    (hf2 : MemLp f 2 Lebesgue.lebesgueFull.μ)
    (hG : Integrable (FullTriple.G Lebesgue.lebesgueFull f f) Lebesgue.lebesgueFull.μ)
    (hG2 : Integrable (Lebesgue.lebesgueFull.toDiffusionTriple.Γ₂ f f) Lebesgue.lebesgueFull.μ) :
    ∃ hF : hf2.toLp f ∈ Lebesgue.lebesgueFull.toDiffusionTriple.generator.domain,
      ((Lebesgue.lebesgueFull.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 Lebesgue.lebesgueFull.μ) : ℝ → ℝ) =ᵐ[Lebesgue.lebesgueFull.μ] Lebesgue.lebesgueFull.L f :=
  FullTriple.mem_domain_of_Γ₂_direct (T := Lebesgue.lebesgueFull) lebesgueDiffusion_isComplete
    Lebesgue.lebesgue_CD_zero_infty hf hf2 hG hG2

/-- **Concrete nontrivial instance**: `f = id` on the OU triple (`𝒜 = C^∞(ℝ) ∌` compactly supported, `id ∉ 𝒜₀`,
`Γ(f) = 1`, `Γ₂(f) = 1`, all hypotheses verified): `[x] ∈ 𝒟(L̄)` and `L̄[x] = [−x]`.  Uses neither `Core2`
nor the Hermite density. -/
theorem OU.ou_id_mem_domain :
    ∃ (hf2 : MemLp (fun x : ℝ => x) 2 OU.ouFull.μ) (hF : hf2.toLp (fun x : ℝ => x) ∈
        OU.ouFull.toDiffusionTriple.generator.domain),
      ((OU.ouFull.toDiffusionTriple.generator ⟨hf2.toLp (fun x : ℝ => x), hF⟩ : Lp ℝ 2 OU.ouFull.μ) : ℝ → ℝ)
        =ᵐ[OU.ouFull.μ] OU.ouFull.L (fun x : ℝ => x) := by
  have hSm : MarkovTriple.Sanity.OU.Sm (fun x : ℝ => x) := contDiff_id
  have hf : (fun x : ℝ => x) ∈ OU.ouFull.A := hSm
  have hf2 : MemLp (fun x : ℝ => x) 2 OU.ouFull.μ :=
    (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 2 : _)
  have hG : Integrable (FullTriple.G OU.ouFull (fun x : ℝ => x) (fun x : ℝ => x)) OU.ouFull.μ := by
    have e : FullTriple.G OU.ouFull (fun x : ℝ => x) (fun x : ℝ => x) = fun _ => 1 := by
      show OU.ouDiff.ΓA _ _ = _
      rw [OU.ouDiff_ΓA hSm hSm]; funext x; simp [MarkovTriple.Sanity.OU.Go]
    rw [e]
    exact integrable_const (μ := MarkovTriple.Sanity.OU.γ) (1 : ℝ)
  have hG2 : Integrable (OU.ouFull.toDiffusionTriple.Γ₂ (fun x : ℝ => x) (fun x : ℝ => x)) OU.ouFull.μ := by
    have e : OU.ouFull.toDiffusionTriple.Γ₂ (fun x : ℝ => x) (fun x : ℝ => x) = fun _ => 1 := by
      funext x; show OU.ouDiff.Γ₂ _ _ x = 1
      rw [OU.ou_Γ₂_eq hSm]; simp
    rw [e]
    exact integrable_const (μ := MarkovTriple.Sanity.OU.γ) (1 : ℝ)
  obtain ⟨hF, h⟩ := OU.ou_mem_domain_of_Γ₂_direct hf hf2 hG hG2
  exact ⟨hf2, hF, h⟩

end MarkovTriple.BGL.Instances

namespace MarkovTriple.BGL.ConverseDirectInst

open MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.BGL.Instances.Riemannian

variable {d : ℕ}

/-- **Direct converse for every `EllData d` with a curvature bound `Curv ρ`, WITHOUT `CoreCut` and without `Core2`**
(compare `EllData.ell_mem_domain_of_Γ₂`, which needs the cut-off family `CoreCut`: bounded `Lχ_n, L²χ_n, Γ(Lχ_n),
Γ₂(χ_n)`).  Completeness (`EllData.diff_isComplete`) only needs `Γχ_n ≤ 1/(n+1)²`. -/
theorem ell_mem_domain_of_Γ₂_direct (E : EllData d) {ρ : ℝ} (hρ : E.Curv ρ) {f : Rd d → ℝ}
    (hf : f ∈ E.fullU.A) (hf2 : MemLp f 2 E.μ)
    (hG : Integrable (FullTriple.G E.fullU f f) E.μ)
    (hG2 : Integrable (E.fullU.toDiffusionTriple.Γ₂ f f) E.μ) :
    ∃ hF : hf2.toLp f ∈ E.fullU.toDiffusionTriple.generator.domain,
      ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ]
        E.fullU.L f :=
  FullTriple.mem_domain_of_Γ₂_direct (T := E.fullU) E.diff_isComplete (E.fullU_CD hρ) hf hf2 hG hG2

/-- Same for weighted Riemannian charts `RiemData d` (compare `RiemData.riem_mem_domain_of_Γ₂`, which needs `CoreCut`);
includes the hyperbolic plane `hypRiem` (no `CoreCut` family exists, ERRATA R19-Ell-2) whenever its `Curv` holds. -/
theorem riem_mem_domain_of_Γ₂_direct (R : RiemData d) {ρ : ℝ} (hρ : R.Curv ρ) {f : Rd d → ℝ}
    (hf : f ∈ R.riemFull_unconditional.A) (hf2 : MemLp f 2 R.toEll.μ)
    (hG : Integrable (FullTriple.G R.riemFull_unconditional f f) R.toEll.μ)
    (hG2 : Integrable (R.riemFull_unconditional.toDiffusionTriple.Γ₂ f f) R.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ R.riemFull_unconditional.toDiffusionTriple.generator.domain,
      ((R.riemFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 R.toEll.μ) :
        Rd d → ℝ) =ᵐ[R.toEll.μ] R.riemFull_unconditional.L f :=
  ell_mem_domain_of_Γ₂_direct R.toEll hρ hf hf2 hG hG2

end MarkovTriple.BGL.ConverseDirectInst
