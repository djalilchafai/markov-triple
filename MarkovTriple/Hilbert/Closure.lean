import Mathlib
import MarkovTriple.Frozen.FullMarkovTriple
import MarkovTriple.Hilbert.Existence
import MarkovTriple.Hilbert.TripleForm

/-!
# Essential self-adjointness: the generator is the closure of `-A|D`

If the range of `1 + A` is dense (the range criterion for essential self-adjointness, used as the
field `FullMarkovTriple.esa`), then the graph of the generator `G = -A_F` of the Friedrichs
semigroup is the closure of the graph of `-A|D`: `G = closure(-A|D)`.  Consequently every
uniqueness of the semigroup among all `IsSemigroupOf` witnesses is *not* proved here; only the
identification of `G` with the closure of `-A|D` is.
-/

open Filter Topology Set MeasureTheory
open scoped NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.Hilbert

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- The graph of `-A|D`. -/
def graphA : Submodule ℝ (H × H) := LinearMap.range (S.D.subtype.prod (-S.A))

lemma graphA_le_graph : S.graphA ≤ S.generator.graph := by
  rintro _ ⟨d, rfl⟩
  obtain ⟨h, hG⟩ := S.generator_extends d
  have := S.generator.mem_graph ⟨(d : H), h⟩
  simp only [hG] at this
  simpa using this

/-- **`G = closure(-A|D)`** when `ran(1 + A)` is dense. -/
theorem graph_generator_eq_closure
    (hd : Dense {y : H | ∃ d : S.D, y = (d : H) + S.A d}) :
    S.generator.graph = S.graphA.topologicalClosure := by
  apply le_antisymm
  · rintro ⟨x, y⟩ hxy
    have hxy' : (x, y) ∈ resolventGeneratorGraph S.R := by
      have := hxy
      rw [show S.generator = resolventGenerator S.R from rfl,
        resolventGenerator_graph S.R S.R_injective] at this
      exact this
    have hR : S.R (x - y) = x := hxy'
    -- approximate `x - y` by `d_n + A d_n`
    have hmem : x - y ∈ closure {w : H | ∃ d : S.D, w = (d : H) + S.A d} := by
      rw [hd.closure_eq]; trivial
    obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.1 hmem
    choose d hd' using hw
    have hdn : ∀ n, S.R (w n) = d n := fun n => by
      rw [hd' n]; exact S.R_resolvent ⟨d n, (d n).2⟩
    have h1 : Tendsto (fun n => (d n : H)) atTop (𝓝 x) := by
      have := (S.R.continuous.tendsto (x - y)).comp hwlim
      rw [hR] at this
      exact this.congr (fun n => hdn n)
    have h2 : Tendsto (fun n => -S.A (d n)) atTop (𝓝 y) := by
      have h3 : Tendsto (fun n => (d n : H) - w n) atTop (𝓝 (x - (x - y))) := h1.sub hwlim
      rw [show x - (x - y) = y by abel] at h3
      refine h3.congr (fun n => ?_)
      rw [hd' n]; abel
    have hlim : Tendsto (fun n => (S.D.subtype.prod (-S.A)) (d n)) atTop (𝓝 (x, y)) :=
      h1.prodMk_nhds h2
    have : (x, y) ∈ closure (S.graphA : Set (H × H)) :=
      mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ⟨d n, rfl⟩)
    rwa [← Submodule.topologicalClosure_coe] at this
  · exact Submodule.topologicalClosure_minimal _ S.graphA_le_graph S.generator_isClosed

end FormData

end MarkovTriple.Hilbert

namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E]

/-- **Essential self-adjointness of `L|𝒜₀` identifies the generator of the triple's semigroup
with the closure of `L|𝒜₀`.** (Uses the field `FullMarkovTriple.esa`.) -/
theorem FullMarkovTriple.generator_graph_eq_closure (F : FullMarkovTriple E) :
    (formData F.toMarkovTriple).generator.graph =
      (formData F.toMarkovTriple).graphA.topologicalClosure := by
  apply (formData F.toMarkovTriple).graph_generator_eq_closure
  refine F.esa.mono ?_
  rintro u ⟨f, hf, huf⟩
  refine ⟨⟨toLp0 F.toMarkovTriple ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩⟩, ?_⟩
  have h1 : (formData F.toMarkovTriple).A ⟨toLp0 F.toMarkovTriple ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩⟩ =
      -Lt0 F.toMarkovTriple ⟨f, hf⟩ := formA_apply _ _
  rw [h1]
  refine Lp.ext ?_
  have hL := F.L_mem f hf
  filter_upwards [huf, coeFn_toLp0 F.toMarkovTriple ⟨f, hf⟩, coeFn_Lt0 F.toMarkovTriple ⟨f, hf⟩,
    Lp.coeFn_add (toLp0 F.toMarkovTriple ⟨f, hf⟩) (-Lt0 F.toMarkovTriple ⟨f, hf⟩),
    Lp.coeFn_neg (Lt0 F.toMarkovTriple ⟨f, hf⟩)] with x e1 e2 e3 e4 e5
  show u x = ((toLp0 F.toMarkovTriple ⟨f, hf⟩ + -Lt0 F.toMarkovTriple ⟨f, hf⟩ : Lp ℝ 2 F.μ) :
    E → ℝ) x
  rw [e1, e4, Pi.add_apply, e5, Pi.neg_apply, e2, e3]
  simp only [Pi.sub_apply]
  ring

end MarkovTriple.Hilbert
