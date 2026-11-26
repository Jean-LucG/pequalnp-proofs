import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19214

private def circuit : PEqualNP.CircuitLowerBounds.Circuit where
  gates := [⟨.or, [4, 5]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [2, 3]⟩,
    ⟨.or, [5, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [9, 12]⟩]
  output := 13

end PEqualNP.Outside.L_meta_19214

theorem PEqualNP.Outside.L_meta_19214 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (989 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19214.circuit, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19214.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
