import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_25389 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6377279 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [8, 11]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [0, 13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel
