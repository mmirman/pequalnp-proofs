import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.OneNotOwnershipObstruction

open PEqualNP.CircuitLowerBounds

abbrev Input := Fin 5 → Bool

def target (x : Input) : Bool := x 0 || x 1 || x 2 || x 3

def single (p : Fin 4) : Input := fun k => decide (k.val = p.val)

def outside : Input := fun k => decide (k = 4)

def Low (f : Input → Bool) := ∀ x, f x = true → target x = true

def High (f : Input → Bool) := ∀ x, target x = true → f x = true

def Good (f : Input → Bool) :=
  (Low f ∨ High f) ∧
  (∃ c d : Fin 4, c ≠ d ∧ f (single c) = true ∧ f (single d) = true) ∧
  f outside = false

-- First contaminate the four-input disjunction with the fifth input.
-- The negative branch removes that contamination.
-- The positive branch restores the answer when the fifth input is true.
def gates : List Gate := [
  ⟨.or, [0, 4]⟩,
  ⟨.or, [5, 1]⟩,
  ⟨.or, [6, 2]⟩,
  ⟨.or, [7, 3]⟩,
  ⟨.not, [4]⟩,
  ⟨.and, [8, 9]⟩,
  ⟨.and, [0, 4]⟩,
  ⟨.and, [1, 4]⟩,
  ⟨.and, [2, 4]⟩,
  ⟨.and, [3, 4]⟩,
  ⟨.or, [11, 12]⟩,
  ⟨.or, [13, 14]⟩,
  ⟨.or, [15, 16]⟩,
  ⟨.or, [10, 17]⟩]

def wire (i : ℕ) (x : Input) : Bool := Circuit.eval ⟨gates, i⟩ (List.ofFn x)

lemma fanInTwo : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2 := by decide

lemma oneNot : ∀ i : Fin gates.length,
    (gates.get i).op = GateOp.not ↔ i.val = 4 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma computes_disjunction : ∀ x : Input, wire 18 x = target x := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma only_two_good_gates : ∀ i : Fin gates.length,
    Good (wire (5 + i.val)) ↔ i.val = 5 ∨ i.val = 13 := by
  decide +kernel

lemma no_third_private_gate : ¬ ∃ i j k : Fin gates.length,
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    Good (wire (5 + i.val)) ∧ Good (wire (5 + j.val)) ∧
    Good (wire (5 + k.val)) := by
  rintro ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩
  have hi' := (only_two_good_gates i).mp hi
  have hj' := (only_two_good_gates j).mp hj
  have hk' := (only_two_good_gates k).mp hk
  have hne (a b : Fin gates.length) (h : a ≠ b) : a.val ≠ b.val :=
    fun he => h (Fin.ext he)
  have := hne i j hij
  have := hne i k hik
  have := hne j k hjk
  omega

end PEqualNP.Outside.OneNotOwnershipObstruction
