import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1577

open PEqualNP.CircuitLowerBounds

-- The evaluator lemmas adapt the checked L-meta-270 proof by k-sandhu.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

def ListBelow (xs ys : List Bool) : Prop :=
  xs.length = ys.length ∧ ∀ i, xs.getD i false = true → ys.getD i false = true

lemma snoc_below {xs ys : List Bool} {b c : Bool} (h : ListBelow xs ys)
    (hbc : b = true → c = true) : ListBelow (xs ++ [b]) (ys ++ [c]) := by
  have hlen := h.1
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hil : i < xs.length
  · rw [List.getD_append _ _ _ _ hil] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h.2 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← h.1]
    by_cases he : i = xs.length
    · subst i
      simpa using hbc (by simpa using hi)
    · have hz : [b].length ≤ i - xs.length := by simp; omega
      rw [List.getD_eq_default _ _ hz] at hi
      contradiction

lemma operation_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (h : ListBelow xs ys) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true]
    intro hx i hi
    exact h.2 i (hx i hi)
  · simp only [hg, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, h.2 i hx⟩

lemma run_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (h : ListBelow xs ys) : ListBelow (run gs xs) (run gs ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun g' hg' => hg g' (by simp [hg']))
      (snoc_below h (operation_mono g (hg g (by simp)) h))

lemma ofFn_below {n : ℕ} (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : ListBelow (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin)] at hi ⊢
    simpa using hxy ⟨i, hin⟩ (by simpa using hi)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)] at hi
    contradiction


lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma value_mono {n : ℕ} (C : Circuit)
    (hops : ∀ h ∈ C.gates, h.op = GateOp.and ∨ h.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  exact (run_mono C.gates hops (ofFn_below x y hxy)).2 w

def OrAncestor (n : ℕ) (gs : List Gate) (a g : ℕ) : Prop :=
  ∀ S : Set ℕ, g ∈ S →
    (∀ i : Fin gs.length, n + (i : ℕ) ∈ S → (gs.get i).op = GateOp.or →
      ∀ r ∈ (gs.get i).inputs, r ∈ S) → a ∈ S

theorem separated_and_atom {n : ℕ} (gs : List Gate)
    (hops : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or)
    (x y z : Fin n → Bool)
    (hcover : ∀ v, z v = true → x v = true ∨ y v = true) :
    ∀ w : ℕ, value ⟨gs, 0⟩ x w = false → value ⟨gs, 0⟩ y w = false →
      value ⟨gs, 0⟩ z w = true →
      ∃ Y : ℕ, OrAncestor n gs Y w ∧
        (∃ i : Fin gs.length, Y = n + (i : ℕ) ∧ (gs.get i).op = GateOp.and) ∧
        value ⟨gs, 0⟩ x Y = false ∧ value ⟨gs, 0⟩ y Y = false ∧
        value ⟨gs, 0⟩ z Y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx hy hz
    have hn : n ≤ w := by
      by_contra hh
      have hwn : w < n := by omega
      let p : Fin n := ⟨w, hwn⟩
      have hzp : z p = true := by simpa only [← input_value ⟨gs, 0⟩ z p] using hz
      have hxp : x p = false := by simpa only [← input_value ⟨gs, 0⟩ x p] using hx
      have hyp : y p = false := by simpa only [← input_value ⟨gs, 0⟩ y p] using hy
      rcases hcover p hzp with h | h <;> simp_all
    have hw : w < n + gs.length := by
      by_contra hh
      have hzfalse := missing_value ⟨gs, 0⟩ z w (by simpa [Circuit.size] using Nat.le_of_not_gt hh)
      rw [hzfalse] at hz
      contradiction
    let i : Fin gs.length := ⟨w - n, by omega⟩
    have hwi : w = n + (i : ℕ) := by dsimp [i]; omega
    rcases hops (gs.get i) (List.get_mem gs i) with hop | hop
    · exact ⟨w, fun S hw _ => hw, ⟨i, hwi, hop⟩, hx, hy, hz⟩
    · have eqv (u : Fin n → Bool) : value ⟨gs, 0⟩ u w =
          ((gs.get i).inputs.map fun r => if r < w then value ⟨gs, 0⟩ u r else false).any id := by
        have he := gate_value (C := ⟨gs, 0⟩) u w hn hw
        change value ⟨gs, 0⟩ u w = (gs.get i).op.eval
          ((gs.get i).inputs.map fun r => if r < w then value ⟨gs, 0⟩ u r else false) at he
        rw [hop] at he
        exact he
      rw [eqv] at hx hy hz
      simp only [List.any_map, List.any_eq_false, Function.comp_apply, id_eq] at hx hy
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hz
      obtain ⟨r, hr, hz⟩ := hz
      have hlt : r < w := by
        by_contra hh
        simp [hh] at hz
      have hxr : value ⟨gs, 0⟩ x r = false := by simpa [hlt] using hx r hr
      have hyr : value ⟨gs, 0⟩ y r = false := by simpa [hlt] using hy r hr
      have hzr : value ⟨gs, 0⟩ z r = true := by simpa [hlt] using hz
      obtain ⟨Y, hanc, hY, hxY, hyY, hzY⟩ := ih r hlt hxr hyr hzr
      refine ⟨Y, ?_, hY, hxY, hyY, hzY⟩
      intro S hwS hS
      apply hanc S _ hS
      exact hS i (hwi ▸ hwS) hop r hr

def line (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def testInput (p v : Fin 13) : Bool :=
  decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ line 0))

lemma line_meet : ∀ t : Fin 13, t ≠ 0 → ((line 0) ∩ line t).card = 1 := by
  decide +kernel

end PEqualNP.Outside.L_meta_1577

open PEqualNP.CircuitLowerBounds

open PEqualNP.Outside.L_meta_1577 in
theorem PEqualNP.Outside.L_meta_1577 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → t ≠ 0 →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
    2 ≤ ((L 0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0)))) = true)).card →
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L t ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true := by
  intro L hL gs g t hops _hback ht hx hy htwo
  have he : L = line := funext hL
  subst L
  have hop : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or := fun h hh => (hops h hh).1
  change value ⟨gs, 0⟩ (fun v => decide (v ∉ line 0)) g = false at hx
  change value ⟨gs, 0⟩ (fun v => decide (v ∉ line t)) g = false at hy
  change 2 ≤ ((line 0).filter (fun p => value ⟨gs, 0⟩ (testInput p) g = true)).card at htwo
  obtain ⟨p, hp, hpnot, hpg⟩ : ∃ p : Fin 13, p ∈ line 0 ∧ p ∉ line t ∧
      value ⟨gs, 0⟩ (testInput p) g = true := by
    by_contra hn
    have hsub : (line 0).filter (fun p => value ⟨gs, 0⟩ (testInput p) g = true) ⊆
        line 0 ∩ line t := by
      intro p hp
      have hpf := Finset.mem_filter.mp hp
      apply Finset.mem_inter.mpr
      refine ⟨hpf.1, ?_⟩
      by_contra hnot
      exact hn ⟨p, hpf.1, hnot, hpf.2⟩
    have hcard := Finset.card_le_card hsub
    rw [line_meet t ht] at hcard
    omega
  have hspecial : p = 3 ∨ p = 9 := by
    by_contra hn
    have hbelow : ∀ v, testInput p v = true → decide (v ∉ line t) = true := by
      intro v hv
      have hvp : v = p := by simpa [testInput, hn] using hv
      subst v
      simp [hpnot]
    have htrue := value_mono ⟨gs, 0⟩ hop (testInput p) (fun v => decide (v ∉ line t)) hbelow g hpg
    rw [hy] at htrue
    contradiction
  have hcover : ∀ v, testInput p v = true →
      decide (v ∉ line 0) = true ∨ decide (v ∉ line t) = true := by
    intro v hv
    simp only [testInput, decide_eq_true_eq] at hv ⊢
    rcases hv with rfl | hv
    · exact Or.inr hpnot
    · exact Or.inl hv.2
  obtain ⟨Y, hanc, hY, hxY, hyY, hzY⟩ :=
    separated_and_atom gs hop _ _ (testInput p) hcover g hx hy hpg
  exact ⟨Y, hanc, hY, hxY, hyY, p, hspecial, hpnot, hzY⟩
