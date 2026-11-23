import Mathlib
import PEqualNP.Defs

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

open PEqualNP.CircuitLowerBounds

lemma getD_ofFn (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by simp

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases he : i = w.length
  · subst i
    simp
  · rw [if_neg he]
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma unused_preserves (gs : List Gate) (k : ℕ)
    (hu : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ k → w.getD i false = w'.getD i false) →
      ∀ i, i ≠ k → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs with
  | nil => intro w w' hl he i hi; exact he i hi
  | cons g gs ih =>
    intro w w' hl he i hi
    have hv : g.op.eval (g.inputs.map fun j => w.getD j false) =
        g.op.eval (g.inputs.map fun j => w'.getD j false) := by
      congr 1
      apply List.map_congr_left
      intro j hj
      apply he j
      intro h
      exact hu g List.mem_cons_self (h ▸ hj)
    apply ih (fun g' hg' => hu g' (List.mem_cons_of_mem g hg'))
      (w ++ [_]) (w' ++ [_]) (by simp [hl]) _ i hi
    intro j hj
    rw [getD_snoc, getD_snoc, hl, hv, he j hj]

lemma input_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), getD_snoc, if_neg (by omega)]

lemma singleton_false : ∀ p : Fin 9, edgeValue (singleton p) = false := by
  decide +kernel

lemma correct_output_not_input (gs : List Gate) (out : ℕ)
    (hc : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = edgeValue x) (p : Fin 9) :
    out ≠ p.val := by
  intro ho
  have h := hc (singleton p)
  change (wiresFrom gs (List.ofFn (singleton p))).getD out false = _ at h
  rw [ho, input_read _ _ _ (by simp), singleton_false] at h
  have ht : (List.ofFn (singleton p)).getD p.val false = true := by
    rw [getD_ofFn]
    simp [singleton]
  rw [ht] at h
  cases h

lemma pair_agree_except (p q : Fin 9) (_hpq : p ≠ q) (a b c : Bool) (x : Input)
    (i : ℕ) (hi : i ≠ q.val) :
    (List.ofFn (setPair p q a b x)).getD i false =
      (List.ofFn (setPair p q a c x)).getD i false := by
  by_cases hn : i < 9
  · rw [List.getD_eq_getElem _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa)]
    simp only [List.getElem_ofFn, setPair]
    have hq : (⟨i, hn⟩ : Fin 9) ≠ q := fun h => hi (congrArg Fin.val h)
    simp [hq]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

-- If the first gate loses a bit, some later gate must read that bit directly.
theorem first_gate_must_reread (gs : List Gate) (g : Gate) (out : ℕ)
    (p q : Fin 9) (hpq : p ≠ q) (a : Bool)
    (hc : ∀ x, (Circuit.mk (g :: gs) out).eval (List.ofFn x) = edgeValue x)
    (hg : ∀ x, g.op.eval (g.inputs.map fun i =>
        (List.ofFn (setPair p q a false x)).getD i false) =
      g.op.eval (g.inputs.map fun i =>
        (List.ofFn (setPair p q a true x)).getD i false)) :
    ∃ h ∈ gs, q.val ∈ h.inputs := by
  by_contra hn
  push Not at hn
  obtain ⟨r, s, _, _, _, _, hprobe⟩ := pair_probes p q hpq
  let x0 := setPair p q a false (singleton s)
  let x1 := setPair p q a true (singleton s)
  have h0 : edgeValue x0 = false := (hprobe a false).2
  have h1 : edgeValue x1 = true := (hprobe a true).2
  have he : (Circuit.mk (g :: gs) out).eval (List.ofFn x0) =
      (Circuit.mk (g :: gs) out).eval (List.ofFn x1) := by
    change (wiresFrom gs ((List.ofFn x0) ++ [_])).getD out false =
      (wiresFrom gs ((List.ofFn x1) ++ [_])).getD out false
    apply unused_preserves gs q.val hn _ _ (by simp) _ out
      (correct_output_not_input (g :: gs) out hc q)
    intro i hi
    rw [getD_snoc, getD_snoc]
    have hv := hg (singleton s)
    have hi' := pair_agree_except p q hpq a false true (singleton s) i hi
    change (if i = 9 then _ else _) = (if i = 9 then _ else _)
    rw [hv, hi']
  rw [hc, hc, h0, h1] at he
  cases he

theorem first_and_rereads_second (gs : List Gate) (out : ℕ)
    (p q : Fin 9) (hpq : p ≠ q)
    (hc : ∀ x, (Circuit.mk (⟨GateOp.and, [p.val, q.val]⟩ :: gs) out).eval
      (List.ofFn x) = edgeValue x) : ∃ h ∈ gs, q.val ∈ h.inputs := by
  apply first_gate_must_reread gs _ out p q hpq false hc
  intro x
  simp only [List.map_cons, List.map_nil, getD_ofFn]
  simp [GateOp.eval, setPair, hpq, Ne.symm hpq]

theorem first_or_rereads_second (gs : List Gate) (out : ℕ)
    (p q : Fin 9) (hpq : p ≠ q)
    (hc : ∀ x, (Circuit.mk (⟨GateOp.or, [p.val, q.val]⟩ :: gs) out).eval
      (List.ofFn x) = edgeValue x) : ∃ h ∈ gs, q.val ∈ h.inputs := by
  apply first_gate_must_reread gs _ out p q hpq true hc
  intro x
  simp only [List.map_cons, List.map_nil, getD_ofFn]
  simp [GateOp.eval, setPair, hpq, Ne.symm hpq]

theorem first_and_rereads_both (gs : List Gate) (out : ℕ)
    (p q : Fin 9) (hpq : p ≠ q)
    (hc : ∀ x, (Circuit.mk (⟨GateOp.and, [p.val, q.val]⟩ :: gs) out).eval
      (List.ofFn x) = edgeValue x) :
    (∃ h ∈ gs, p.val ∈ h.inputs) ∧ (∃ h ∈ gs, q.val ∈ h.inputs) := by
  constructor
  · apply first_gate_must_reread gs _ out q p hpq.symm false hc
    intro x
    simp only [List.map_cons, List.map_nil, getD_ofFn]
    simp [GateOp.eval, setPair, hpq, Ne.symm hpq]
  · exact first_and_rereads_second gs out p q hpq hc

theorem first_or_rereads_both (gs : List Gate) (out : ℕ)
    (p q : Fin 9) (hpq : p ≠ q)
    (hc : ∀ x, (Circuit.mk (⟨GateOp.or, [p.val, q.val]⟩ :: gs) out).eval
      (List.ofFn x) = edgeValue x) :
    (∃ h ∈ gs, p.val ∈ h.inputs) ∧ (∃ h ∈ gs, q.val ∈ h.inputs) := by
  constructor
  · apply first_gate_must_reread gs _ out q p hpq.symm true hc
    intro x
    simp only [List.map_cons, List.map_nil, getD_ofFn]
    simp [GateOp.eval, setPair, hpq, Ne.symm hpq]
  · exact first_or_rereads_second gs out p q hpq hc

end PEqualNP.Outside.PetersenInterfaces
