import Mathlib

/-!
# Round 22 (E3): the one-point compactification of a locally compact second countable
Hausdorff space is second countable (not in Mathlib).
-/

open Set TopologicalSpace Topology

namespace MarkovTriple.Stochastic.R22

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X]

/-- The one-point compactification of a locally compact second countable Hausdorff space is
second countable. -/
instance secondCountableOnePoint : SecondCountableTopology (OnePoint X) := by
  obtain ⟨B, hBc, -, hBb⟩ := TopologicalSpace.exists_countable_basis X
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let 𝓑 : Set (Set (OnePoint X)) :=
    ((fun b : Set X => ((↑) : X → OnePoint X) '' b) '' B) ∪
      Set.range (fun n : ℕ => (((↑) : X → OnePoint X) '' (K n))ᶜ)
  have hcount : 𝓑.Countable := (hBc.image _).union (Set.countable_range _)
  have hbasis : IsTopologicalBasis 𝓑 := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro u (⟨b, hb, rfl⟩ | ⟨n, rfl⟩)
      · exact OnePoint.isOpenMap_coe _ (hBb.isOpen hb)
      · exact OnePoint.isOpen_compl_image_coe.2 ⟨(K.isCompact n).isClosed, K.isCompact n⟩
    · intro a u ha hu
      induction a using OnePoint.rec with
      | infty =>
        rw [OnePoint.isOpen_iff_of_mem ha] at hu
        obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hu.2
        refine ⟨_, Or.inr ⟨n, rfl⟩, ?_, ?_⟩
        · exact fun ⟨y, _, hy⟩ => OnePoint.infty_ne_coe y hy.symm
        · intro a ha'
          induction a using OnePoint.rec with
          | infty => exact ha
          | coe y =>
            by_contra hyu
            exact ha' ⟨y, hn hyu, rfl⟩
      | coe x =>
        have hx : x ∈ ((↑) : X → OnePoint X) ⁻¹' u := ha
        obtain ⟨b, hb, hxb, hbu⟩ := hBb.exists_subset_of_mem_open hx (hu.preimage OnePoint.continuous_coe)
        exact ⟨_, Or.inl ⟨b, hb, rfl⟩, ⟨x, hxb, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hbu hy⟩
  exact hbasis.secondCountableTopology hcount

end MarkovTriple.Stochastic.R22
