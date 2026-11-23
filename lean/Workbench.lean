import Mathlib
import PEqualNP.Defs

namespace PNPWorkbench

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def upper : Circuit := ⟨[
  ⟨.or, [1, 4]⟩,
  ⟨.or, [9, 5]⟩,
  ⟨.and, [0, 10]⟩,
  ⟨.or, [2, 6]⟩,
  ⟨.and, [1, 12]⟩,
  ⟨.or, [2, 4]⟩,
  ⟨.or, [14, 8]⟩,
  ⟨.and, [3, 15]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.and, [7, 17]⟩,
  ⟨.or, [6, 5]⟩,
  ⟨.and, [8, 19]⟩,
  ⟨.or, [11, 13]⟩,
  ⟨.or, [21, 16]⟩,
  ⟨.or, [22, 18]⟩,
  ⟨.or, [23, 20]⟩], 24⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem upper_correct : HasCircuitSize 9 target 16 := by
  refine ⟨upper, ?_, ?_, ?_⟩
  · simp [FanInTwo, upper]
  · decide
  · decide

end PNPWorkbench
