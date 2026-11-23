import Mathlib
import PEqualNP.Defs

namespace PNPMatchingWorkbench

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upper : Circuit := ⟨[
  ⟨.and, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩,
  ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩,
  ⟨.and, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 3]⟩,
  ⟨.or, [11, 12]⟩, ⟨.or, [14, 13]⟩,
  ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [2, 4]⟩,
  ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 10⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem upper_correct :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 15 ∧ ∃ o0 o1 o2 : ℕ,
      ∀ x : Fin 6 → Bool,
        (C.wires (List.ofFn x)).getD o0 false =
          ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧
        (C.wires (List.ofFn x)).getD o1 false =
          ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧
        (C.wires (List.ofFn x)).getD o2 false =
          ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4)) := by
  refine ⟨upper, ?_, ?_, 10, 15, 20, ?_⟩
  · simp [FanInTwo, upper]
  · decide
  · decide +kernel

end PNPMatchingWorkbench
