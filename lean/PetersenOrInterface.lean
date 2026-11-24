import Mathlib

namespace PEqualNP.Outside.PetersenOrInterface

def edgeValue (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def setFour (s : Fin 4 → Bool) (rest : Fin 10 → Bool) : Fin 10 → Bool :=
  fun i => if i = 0 then s 0 else if i = 1 then s 1 else
    if i = 3 then s 2 else if i = 7 then s 3 else rest i

def state (i : Fin 9) : Fin 4 → Bool :=
  fun j => Nat.testBit ((![(1 : ℕ), 2, 3, 5, 6, 9, 10, 13, 14] : Fin 9 → ℕ) i) j.val

def probe (r : Fin 4) : Fin 10 → Bool :=
  fun i => if r = 0 then false else
    decide (i = ((![(0 : Fin 10), 6, 8, 9] : Fin 4 → Fin 10) r))

lemma state_or_true : ∀ i : Fin 9, (state i 0 || state i 1) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma probes_distinguish : ∀ i j : Fin 9,
    (∀ r : Fin 4, edgeValue (setFour (state i) (probe r)) =
      edgeValue (setFour (state j) (probe r))) → i = j := by
  decide +kernel

-- Once the first bit is fixed to true, the remaining summary must distinguish nine states.
theorem retained_or_needs_nine_states {α : Type*} [Fintype α]
    (encode : (Fin 4 → Bool) → α)
    (decode : Bool → α → (Fin 10 → Bool) → Bool)
    (correct : ∀ s rest, decode (s 0 || s 1) (encode s) rest = edgeValue (setFour s rest)) :
    9 ≤ Fintype.card α := by
  have injective : Function.Injective (fun i : Fin 9 => encode (state i)) := by
    intro i j same
    apply probes_distinguish i j
    intro r
    rw [← correct, ← correct, state_or_true, state_or_true, same]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ injective

theorem three_extra_bits_are_insufficient :
    ¬ ∃ (encode : (Fin 4 → Bool) → (Fin 3 → Bool))
      (decode : Bool → (Fin 3 → Bool) → (Fin 10 → Bool) → Bool),
      ∀ s rest, decode (s 0 || s 1) (encode s) rest = edgeValue (setFour s rest) := by
  rintro ⟨encode, decode, correct⟩
  have bound := retained_or_needs_nine_states encode decode correct
  norm_num at bound

end PEqualNP.Outside.PetersenOrInterface
