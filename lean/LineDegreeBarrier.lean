import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LineDegreeBarrier

open PEqualNP.CircuitLowerBounds

def target (x : Fin 5 → Bool) : Bool := x 0 && (x 1 || x 2 || x 3 || x 4)

def circuit : Circuit where
  gates := [
    ⟨.or, [0, 2]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.or, [10, 2]⟩,
    ⟨.or, [11, 3]⟩,
    ⟨.or, [12, 4]⟩,
    ⟨.and, [0, 13]⟩]
  output := 14

def value (x : Fin 5 → Bool) (w : ℕ) : Bool :=
  (circuit.wires (List.ofFn x)).getD w false

lemma correct : ∀ x : Fin 5 → Bool, circuit.eval (List.ofFn x) = target x := by
  decide +kernel

lemma gates_are_monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

lemma size : circuit.size = 10 := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma all_inputs_essential : ∀ p : Fin 5,
    ∃ x y : Fin 5 → Bool, (∀ q : Fin 5, q ≠ p → x q = y q) ∧
      circuit.eval (List.ofFn x) ≠ circuit.eval (List.ofFn y) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma wires_are_distinct : ∀ i j : Fin 15,
    (∀ x : Fin 5 → Bool, value x i = value x j) → i = j := by
  decide +kernel

lemma gates_read_earlier_wires : ∀ j : Fin 10,
    ∀ w ∈ (circuit.gates.get j).inputs, w < 5 + j.val := by
  decide +kernel

lemma every_nonoutput_gate_is_read : ∀ j : Fin 9, ∃ k : Fin 10,
    j.val < k.val ∧ 5 + j.val ∈ (circuit.gates.get k).inputs := by
  decide +kernel

lemma gates_are_not_copies : ∀ j : Fin 10,
    ∀ w ∈ (circuit.gates.get j).inputs,
      ∃ x : Fin 5 → Bool, value x (5 + j.val) ≠ value x w := by
  decide +kernel

lemma no_and_factor_is_sound : ∀ j : Fin 10,
    (circuit.gates.get j).op = GateOp.and →
      ∀ w ∈ (circuit.gates.get j).inputs,
        ∃ x : Fin 5 → Bool, value x w = true ∧ target x = false := by
  intro j
  fin_cases j <;> simp [circuit] <;> decide +kernel

lemma output_line_degree : circuit.lineDeg 5 {1, 2, 3, 4} = 4 := by
  decide +kernel

theorem not_line_degree_three : ¬ HasLineDegree 5 {1, 2, 3, 4} circuit 3 := by
  unfold HasLineDegree
  rw [output_line_degree]
  omega

def shorter : Circuit where
  gates := [⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩]
  output := 8

lemma shorter_correct : ∀ x : Fin 5 → Bool, shorter.eval (List.ofFn x) = target x := by
  decide +kernel

lemma shorter_size : shorter.size = 4 := by rfl

-- This example obstructs a local cleanup argument, not a cost-preserving global normalization.
theorem not_a_least_circuit : shorter.size < circuit.size ∧
    ∀ x : Fin 5 → Bool, shorter.eval (List.ofFn x) = circuit.eval (List.ofFn x) := by
  constructor
  · decide
  · intro x
    rw [correct, shorter_correct]

end PEqualNP.Outside.LineDegreeBarrier

namespace PEqualNP.Outside.LineDegreeBarrier.Matching

open PEqualNP.CircuitLowerBounds

def target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)

def circuit : Circuit where
  gates := [
    ⟨.or, [0, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 3]⟩,
    ⟨.or, [6, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [7, 5]⟩,
    ⟨.or, [8, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [9, 5]⟩,
    ⟨.and, [10, 11]⟩, ⟨.and, [12, 13]⟩,
    ⟨.and, [14, 15]⟩, ⟨.and, [16, 17]⟩,
    ⟨.and, [18, 19]⟩, ⟨.and, [20, 21]⟩, ⟨.and, [22, 23]⟩]
  output := 24

def value (x : Fin 6 → Bool) (w : ℕ) : Bool :=
  (circuit.wires (List.ofFn x)).getD w false

def bypass (j w : ℕ) : Circuit :=
  ⟨circuit.gates.set j ⟨.or, [w, w]⟩, circuit.output⟩

lemma correct : ∀ x : Fin 6 → Bool, circuit.eval (List.ofFn x) = target x := by
  decide +kernel

lemma gates_are_monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma wires_are_distinct : ∀ i j : Fin 25,
    (∀ x : Fin 6 → Bool, value x i = value x j) → i = j := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem no_output_preserving_single_gate_bypass : ∀ j : Fin 19,
    ∀ w ∈ (circuit.gates.get j).inputs,
      ∃ x : Fin 6 → Bool, (bypass j.val w).eval (List.ofFn x) ≠ target x := by
  decide +kernel

lemma output_line_degree : circuit.lineDeg 6 {1, 3, 5} = 7 := by
  decide +kernel

def shorter : Circuit where
  gates := [⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩]
  output := 10

lemma shorter_correct : ∀ x : Fin 6 → Bool, shorter.eval (List.ofFn x) = target x := by
  decide +kernel

theorem not_a_least_circuit : shorter.size = 5 ∧ circuit.size = 19 ∧
    ∀ x : Fin 6 → Bool, shorter.eval (List.ofFn x) = circuit.eval (List.ofFn x) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  rw [correct, shorter_correct]

end PEqualNP.Outside.LineDegreeBarrier.Matching
