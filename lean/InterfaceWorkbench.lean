import Mathlib

namespace PEqualNP.Outside.PetersenInterfaces

abbrev Input := Fin 9 → Bool

def edgeValue (x : Input) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def setPair (p q : Fin 9) (a b : Bool) (x : Input) : Input :=
  fun v => if v = p then a else if v = q then b else x v

def singleton (r : Fin 9) : Input := fun v => decide (v = r)

-- A singleton outside either pair can expose either bit of that pair.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem pair_probes : ∀ p q : Fin 9, p ≠ q →
    ∃ r s : Fin 9, r ≠ p ∧ r ≠ q ∧ s ≠ p ∧ s ≠ q ∧
      ∀ a b : Bool,
        edgeValue (setPair p q a b (singleton r)) = a ∧
        edgeValue (setPair p q a b (singleton s)) = b := by
  decide +kernel

theorem all_pair_cofactors_distinct (p q : Fin 9) (hpq : p ≠ q)
    (a b c d : Bool)
    (h : ∀ x, edgeValue (setPair p q a b x) = edgeValue (setPair p q c d x)) :
    a = c ∧ b = d := by
  obtain ⟨r, s, _, _, _, _, hprobe⟩ := pair_probes p q hpq
  constructor
  · have he := h (singleton r)
    simpa only [(hprobe a b).1, (hprobe c d).1] using he
  · have he := h (singleton s)
    simpa only [(hprobe a b).2, (hprobe c d).2] using he

-- This is a semantic condition on an interface, independent of the gate basis.
theorem pair_summary_injective {S : Type} (p q : Fin 9) (hpq : p ≠ q)
    (encode : Bool × Bool → S) (decode : S → Input → Bool)
    (h : ∀ a b x, decode (encode (a, b)) x = edgeValue (setPair p q a b x)) :
    Function.Injective encode := by
  rintro ⟨a, b⟩ ⟨c, d⟩ he
  obtain ⟨ha, hb⟩ := all_pair_cofactors_distinct p q hpq a b c d (by
    intro x
    rw [← h a b x, ← h c d x, he])
  exact Prod.ext ha hb

theorem no_single_bit_pair_summary (p q : Fin 9) (hpq : p ≠ q)
    (encode : Bool × Bool → Bool) (decode : Bool → Input → Bool) :
    ¬ ∀ a b x, decode (encode (a, b)) x = edgeValue (setPair p q a b x) := by
  intro h
  have hc := Fintype.card_le_of_injective encode (pair_summary_injective p q hpq encode decode h)
  norm_num at hc

-- Keeping the first input does not rescue a summary which loses the second.
theorem no_absorbing_pair_summary (p q : Fin 9) (hpq : p ≠ q)
    (op : Bool → Bool → Bool) (a z : Bool) (habs : ∀ b, op a b = z)
    (decode : Bool → Bool → Input → Bool) :
    ¬ ∀ b x, decode a (op a b) x = edgeValue (setPair p q a b x) := by
  intro h
  have he : ∀ x,
      edgeValue (setPair p q a false x) = edgeValue (setPair p q a true x) := by
    intro x
    rw [← h false x, ← h true x, habs false, habs true]
  have hh := (all_pair_cofactors_distinct p q hpq a false a true he).2
  cases hh

def bridgeInput (a : Fin 3 → Bool) (x : Input) : Input :=
  fun v => if v = 4 then a 0 else if v = 6 then a 1 else if v = 7 then a 2 else x v

-- Vertices 0, 1, and 2 separately read the three subdivision inputs.
theorem bridge_probes (a : Fin 3 → Bool) (j : Fin 3) :
    edgeValue (bridgeInput a (singleton ⟨j.val, by omega⟩)) = a j := by
  fin_cases j <;> simp [edgeValue, bridgeInput, singleton]

theorem bridge_summary_injective {S : Type}
    (encode : (Fin 3 → Bool) → S) (decode : S → Input → Bool)
    (h : ∀ a x, decode (encode a) x = edgeValue (bridgeInput a x)) :
    Function.Injective encode := by
  intro a b he
  funext j
  have hr : edgeValue (bridgeInput a (singleton ⟨j.val, by omega⟩)) =
      edgeValue (bridgeInput b (singleton ⟨j.val, by omega⟩)) := by
    rw [← h, ← h, he]
  simpa only [bridge_probes] using hr

theorem bridge_summary_needs_eight_states {S : Type} [Fintype S]
    (encode : (Fin 3 → Bool) → S) (decode : S → Input → Bool)
    (h : ∀ a x, decode (encode a) x = edgeValue (bridgeInput a x)) :
    8 ≤ Fintype.card S := by
  have hc := Fintype.card_le_of_injective encode (bridge_summary_injective encode decode h)
  simpa using hc

theorem no_two_bit_bridge_summary
    (encode : (Fin 3 → Bool) → (Fin 2 → Bool)) (decode : (Fin 2 → Bool) → Input → Bool) :
    ¬ ∀ a x, decode (encode a) x = edgeValue (bridgeInput a x) := by
  intro h
  have hc := bridge_summary_needs_eight_states encode decode h
  norm_num at hc

end PEqualNP.Outside.PetersenInterfaces
