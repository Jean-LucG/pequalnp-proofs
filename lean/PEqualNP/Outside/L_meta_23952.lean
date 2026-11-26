import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_23952 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (5022 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[
    ⟨.or,  [3, 4]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.or,  [2, 5]⟩,
    ⟨.not, [5]⟩,
    ⟨.or,  [1, 8]⟩,
    ⟨.or,  [0, 9]⟩,
    ⟨.and, [7, 10]⟩,
    ⟨.or,  [6, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel
