import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.AndAncestor

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

def Closed (n : ℕ) (gs : List Gate) (T : Finset (Fin gs.length)) : Prop :=
  ∀ i ∈ T, ∀ j : Fin gs.length, n + (j : ℕ) ∈ (gs.get i).inputs → j < i → j ∈ T

def Ancestor (n : ℕ) (gs : List Gate) (a g : Fin gs.length) : Prop :=
  ∀ T : Finset (Fin gs.length), g ∈ T → Closed n gs T → a ∈ T

theorem and_ancestor_of_separation {n : ℕ} (gs : List Gate)
    (hops : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or)
    (x y z : Fin n → Bool)
    (hcover : ∀ v, z v = true → x v = true ∨ y v = true)
    (g : Fin gs.length)
    (hx : value ⟨gs, 0⟩ x (n + g) = false)
    (hy : value ⟨gs, 0⟩ y (n + g) = false)
    (hz : value ⟨gs, 0⟩ z (n + g) = true) :
    ∃ a : Fin gs.length, (gs.get a).op = GateOp.and ∧ Ancestor n gs a g := by
  have main : ∀ w : ℕ, ∀ hn : n ≤ w, ∀ hw : w < n + gs.length,
      value ⟨gs, 0⟩ x w = false → value ⟨gs, 0⟩ y w = false →
      value ⟨gs, 0⟩ z w = true →
      ∃ a : Fin gs.length, (gs.get a).op = GateOp.and ∧
        Ancestor n gs a ⟨w - n, by omega⟩ := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hn hw hx hy hz
      let i : Fin gs.length := ⟨w - n, by omega⟩
      rcases hops (gs.get i) (List.get_mem gs i) with hop | hop
      · exact ⟨i, hop, fun T hi _ => hi⟩
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
        have hrn : n ≤ r := by
          by_contra hh
          have hrn : r < n := by omega
          let p : Fin n := ⟨r, hrn⟩
          have hzp : z p = true := by simpa only [← input_value ⟨gs, 0⟩ z p] using hzr
          have hxp : x p = false := by simpa only [← input_value ⟨gs, 0⟩ x p] using hxr
          have hyp : y p = false := by simpa only [← input_value ⟨gs, 0⟩ y p] using hyr
          rcases hcover p hzp with h | h <;> simp_all
        obtain ⟨a, ha, hanc⟩ := ih r hlt hrn (by omega) hxr hyr hzr
        refine ⟨a, ha, ?_⟩
        intro T hi hT
        apply hanc T _ hT
        apply hT i hi ⟨r - n, by omega⟩
        · have he : n + (r - n) = r := by omega
          simpa only [he] using hr
        · change r - n < w - n
          omega
  simpa using main (n + g) (by omega) (by omega) hx hy hz

theorem intersecting_tests_need_and {n : ℕ} (L M : Finset (Fin n)) (m : Fin n)
    (B : Fin n → Finset (Fin n)) (gs : List Gate) (g : Fin gs.length) (q q' : Fin n)
    (hmeet : L ∩ M = {m}) (hB : ∀ r ∈ L, B r ∩ L = ∅)
    (hops : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hq : q ∈ L) (hq' : q' ∈ L) (hne : q ≠ q')
    (hx : value ⟨gs, 0⟩ (fun v => decide (v ∉ L)) (n + g) = false)
    (hy : value ⟨gs, 0⟩ (fun v => decide (v ∉ M)) (n + g) = false)
    (hz : value ⟨gs, 0⟩ (fun v => decide (v = q ∨ v ∈ B q)) (n + g) = true)
    (hz' : value ⟨gs, 0⟩ (fun v => decide (v = q' ∨ v ∈ B q')) (n + g) = true) :
    ∃ a : Fin gs.length, (gs.get a).op = GateOp.and ∧ Ancestor n gs a g := by
  obtain ⟨r, hrL, hrm, hrt⟩ : ∃ r : Fin n, r ∈ L ∧ r ≠ m ∧
      value ⟨gs, 0⟩ (fun v => decide (v = r ∨ v ∈ B r)) (n + g) = true := by
    by_cases hqm : q = m
    · refine ⟨q', hq', ?_, hz'⟩
      intro hq'm
      exact hne (hqm.trans hq'm.symm)
    · exact ⟨q, hq, hqm, hz⟩
  apply and_ancestor_of_separation gs hops _ _ _ _ g hx hy hrt
  intro v hv
  simp only [decide_eq_true_eq] at hv ⊢
  by_cases hvL : v ∈ L
  · right
    intro hvM
    have hvm : v = m := by
      have hmem : v ∈ L ∩ M := Finset.mem_inter.mpr ⟨hvL, hvM⟩
      rw [hmeet] at hmem
      exact Finset.mem_singleton.mp hmem
    rcases hv with hvr | hvB
    · exact hrm (hvr.symm.trans hvm)
    · have hmem := Finset.mem_inter.mpr ⟨hvB, hvL⟩
      rw [hB r hrL] at hmem
      exact Finset.notMem_empty _ hmem
  · exact Or.inl hvL

theorem L1557_exact : ∀ (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (B : Fin n → Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : Fin gates.length) (q q' : Fin n),
    L ∩ M = {m} → (∀ r ∈ L, B r ∩ L = ∅) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    q ∈ L → q' ∈ L → q ≠ q' →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = q ∨ v ∈ B q))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = q' ∨ v ∈ B q'))) = true →
    ∃ a : Fin gates.length, (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ∀ T : Finset (Fin gates.length), g ∈ T →
        (∀ i ∈ T, ∀ g' : Fin gates.length, n + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → a ∈ T := by
  intro n L M m B gs g q q' hmeet hB hops hq hq' hne hx hy hz hz'
  exact intersecting_tests_need_and L M m B gs g q q' hmeet hB
    (fun h hh => (hops h hh).1) hq hq' hne hx hy hz hz'

end PEqualNP.Outside.AndAncestor
