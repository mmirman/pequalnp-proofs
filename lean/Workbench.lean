import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1019

open PEqualNP.CircuitLowerBounds

abbrev V := Fin 13

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def firstRep (R : List V) (g : Gate) : V := R.getD (g.inputs.getD 0 0) 0
def secondRep (R : List V) (g : Gate) : V := R.getD (g.inputs.getD 1 0) 0

def trace : List Gate → List V → List V × List (Sym2 V)
  | [], R => (R, [])
  | g :: gs, R =>
      let t := trace gs (R ++ [firstRep R g])
      (t.1, s(firstRep R g, secondRep R g) :: t.2)

def graph (E : List (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (E.toFinset : Set (Sym2 V))

lemma trace_length (gs : List Gate) (R : List V) : (trace gs R).2.length = gs.length := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih => simp [trace, ih]

lemma getD_snoc_ne {α : Type} (L : List α) (a d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [a]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by simp

def Agree (G : SimpleGraph V) (x y : V → Bool) (R : List V) (w w' : List Bool) : Prop :=
  R.length = w.length ∧ w.length = w'.length ∧
    ∀ j, (∀ v, G.Reachable (R.getD j 0) v → x v = y v) →
      w.getD j false = w'.getD j false

lemma operand_reachable (G : SimpleGraph V) (R : List V) (g : Gate)
    (hg : g.inputs.length ≤ 2) (he : G.Reachable (firstRep R g) (secondRep R g))
    (a : ℕ) (ha : a ∈ g.inputs) : G.Reachable (firstRep R g) (R.getD a 0) := by
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil => simp at ha
  | cons i ins =>
    cases ins with
    | nil =>
      have hai : a = i := by simpa using ha
      subst a
      exact .rfl
    | cons j ins =>
      cases ins with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact .rfl
        · exact he
      | cons k ins => simp at hg

lemma agree_step (G : SimpleGraph V) (x y : V → Bool) (R : List V)
    (w w' : List Bool) (g : Gate) (hg : g.inputs.length ≤ 2)
    (he : G.Reachable (firstRep R g) (secondRep R g))
    (h : Agree G x y R w w') :
    Agree G x y (R ++ [firstRep R g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp [h1], by simp [h2], ?_⟩
  intro j hj
  by_cases hjl : j = R.length
  · subst j
    rw [getD_snoc_eq] at hj
    rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro a ha
    apply h3 a
    intro v hv
    exact hj v ((operand_reachable G R g hg he a ha).trans hv)
  · rw [getD_snoc_ne _ _ _ _ hjl] at hj
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    exact h3 j hj

lemma agree_trace (G : SimpleGraph V) (x y : V → Bool) (gs : List Gate) :
    ∀ (R : List V) (w w' : List Bool),
      (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (∀ a b, s(a, b) ∈ (trace gs R).2 → G.Reachable a b) →
      Agree G x y R w w' →
      Agree G x y (trace gs R).1 (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro R w w' _ _ h; exact h
  | cons g gs ih =>
    intro R w w' hg he h
    apply ih (R ++ [firstRep R g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem g hg')
    · intro a b hab
      exact he a b (by simp only [trace, List.mem_cons]; exact Or.inr hab)
    · apply agree_step G x y R w w' g (hg g List.mem_cons_self) _ h
      exact he _ _ (by simp [trace])

def inputReps : List V := List.ofFn id

lemma getD_ofFn {α : Type} (n : ℕ) (f : Fin n → α) (d : α) (j : Fin n) :
    (List.ofFn f).getD j d = f j := by simp

lemma agree_inputs (G : SimpleGraph V) (x y : V → Bool) :
    Agree G x y inputReps (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputReps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < 13
  · have hr : inputReps.getD j 0 = ⟨j, hjn⟩ := getD_ofFn 13 id 0 ⟨j, hjn⟩
    have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by rw [hr])
    rw [getD_ofFn 13 x false ⟨j, hjn⟩, getD_ofFn 13 y false ⟨j, hjn⟩]
    exact hx
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma graph_reachable (E : List (Sym2 V)) (a b : V) (h : s(a, b) ∈ E) :
    (graph E).Reachable a b := by
  by_cases hab : a = b
  · subst b; exact .rfl
  · apply SimpleGraph.Adj.reachable
    exact ⟨List.mem_toFinset.mpr h, hab⟩

lemma dependence (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (o : ℕ) (v : V) (x y : V → Bool)
    (hxy : ∀ j, j ≠ v → x j = y j)
    (hne : (Circuit.mk gs o).eval (List.ofFn x) ≠ (Circuit.mk gs o).eval (List.ofFn y)) :
    (graph (trace gs inputReps).2).Reachable ((trace gs inputReps).1.getD o 0) v := by
  by_contra hn
  apply hne
  have h := agree_trace (graph (trace gs inputReps).2) x y gs inputReps
    (List.ofFn x) (List.ofFn y) hg (graph_reachable _) (agree_inputs _ _ _)
  exact h.2.2 o (fun j hj => hxy j (fun e => hn (e ▸ hj)))

lemma component_bound (E : List (Sym2 V)) (A : Finset V)
    (h : ∀ v ∈ A, (graph E).Reachable 0 v) : A.card ≤ E.length + 1 := by
  classical
  let G := graph E
  let C := G.connectedComponentMk 0
  have hsub : (A : Set V) ⊆ C.supp := by
    intro v hv
    exact SimpleGraph.ConnectedComponent.sound (h v hv).symm
  have hA : A.card ≤ Nat.card C := by
    simpa only [Set.ncard_coe_finset, SimpleGraph.ConnectedComponent.ncard_supp] using
      Set.ncard_le_ncard hsub
  have hC := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  have hCG : Nat.card C.toSimpleGraph.edgeSet ≤ Nat.card G.edgeSet :=
    Nat.card_le_card_of_injective C.toSimpleGraph_hom.mapEdgeSet
      (SimpleGraph.Hom.mapEdgeSet.injective _ Subtype.val_injective)
  have hGE : Nat.card G.edgeSet ≤ E.toFinset.card := by
    change G.edgeSet.ncard ≤ E.toFinset.card
    have hs : G.edgeSet ⊆ (E.toFinset : Set (Sym2 V)) := by
      rw [show G = SimpleGraph.fromEdgeSet (E.toFinset : Set (Sym2 V)) from rfl,
        SimpleGraph.edgeSet_fromEdgeSet]
      exact Set.sdiff_subset
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hs
  have hEL := List.toFinset_card_le E
  omega

def shifts : Fin 3 → Fin 13 := ![0, 12, 10]
def line (i : Fin 3) : Finset V := ({0, 1, 3, 9} : Finset V).image (fun u => u + shifts i)
def value (i : Fin 3) (x : V → Bool) : Bool := decide (∀ v ∈ line i, x v = true)
def band (x : V → Bool) : Prop :=
  (Finset.univ.filter (fun i => x i = true)).card = 6 ∨
    (Finset.univ.filter (fun i => x i = true)).card = 7
def witnessX (i : Fin 3) (v : V) : Bool := decide (v ∈ line i ∪ {4, 5, 7})
def witnessY (i : Fin 3) (v j : V) : Bool := witnessX i j && decide (j ≠ v)
def used : Finset V := {0, 1, 2, 3, 6, 8, 9, 10, 11, 12}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma witnesses : ∀ (i : Fin 3) (v : V), v ∈ line i →
    band (witnessX i) ∧ band (witnessY i v) ∧
    (∀ j, j ≠ v → witnessX i j = witnessY i v j) ∧
    value i (witnessX i) ≠ value i (witnessY i v) := by
  unfold band value
  decide +kernel

lemma main (gs : List Gate) (out : Fin 3 → ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (he : ∀ x : V → Bool, band x → ∀ i : Fin 3,
      (Circuit.mk gs (out i)).eval (List.ofFn x) = value i x) : 9 ≤ gs.length := by
  let E := (trace gs inputReps).2
  have hr (i : Fin 3) (v : V) (hv : v ∈ line i) :
      (graph E).Reachable ((trace gs inputReps).1.getD (out i) 0) v := by
    obtain ⟨hx, hy, hxy, hne⟩ := witnesses i v hv
    exact dependence gs hg (out i) v _ _ hxy (by rw [he _ hx i, he _ hy i]; exact hne)
  have hz : ∀ i : Fin 3, (0 : V) ∈ line i := by decide
  have hu : ∀ v ∈ used, ∃ i : Fin 3, v ∈ line i := by decide
  have hb := component_bound E used (by
    intro v hv
    obtain ⟨i, hi⟩ := hu v hv
    exact (hr i 0 (hz i)).symm.trans (hr i v hi))
  have hc : used.card = 10 := by decide
  have hl : E.length = gs.length := trace_length gs inputReps
  omega

end PEqualNP.Outside.L_meta_1019

theorem PEqualNP.Outside.L_meta_1019 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 3 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin 13 → Bool, ((Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 6 ∨ (Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 7) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 0⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 0)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 1⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 12)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 2⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 10)), x v = true)) → 9 ≤ gates.length := by
  intro gs out hg he
  apply PEqualNP.Outside.L_meta_1019.main gs out (fun g h => (hg g h).2)
  intro x hx i
  have h := he x hx
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2
