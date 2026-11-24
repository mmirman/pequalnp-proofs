import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.PairCleaning

open PEqualNP.CircuitLowerBounds

def Below {X : Type} (f g : X → Bool) : Prop :=
  ∀ x, f x = true → g x = true

def Positive {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def pair {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun w => decide (w = u ∨ w = v)

def target {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : Bool :=
  decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

lemma pair_below {n : ℕ} (x : Fin n → Bool) (u v : Fin n)
    (hu : x u = true) (hv : x v = true) :
    ∀ i, pair u v i = true → x i = true := by
  intro i hi
  simp only [pair, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl <;> assumption

lemma pair_target {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : target G (pair u v) = true := by
  apply decide_eq_true
  exact ⟨u, v, huv, by simp [pair], by simp [pair]⟩

lemma minterm_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : (Fin n → Bool) → Bool → Bool) (h h' : (Fin n → Bool) → Bool)
    (hF : ∀ x y, (∀ i, x i = true → y i = true) →
      ∀ b c, (b = true → c = true) → F x b = true → F y c = true)
    (hmono : Positive h') (hdown : Below h' h)
    (hpairs : ∀ u v, G.Adj u v → h' (pair u v) = h (pair u v))
    (hcorrect : ∀ x, F x (h x) = target G x) :
    ∀ x, F x (h' x) = target G x := by
  intro x
  cases ht : target G x with
  | false =>
    cases hn : F x (h' x) with
    | false => rfl
    | true =>
      have hh := hF x x (fun _ hi => hi) (h' x) (h x) (hdown x) hn
      rw [hcorrect, ht] at hh
      contradiction
  | true =>
    obtain ⟨u, v, huv, hu, hv⟩ := of_decide_eq_true ht
    have hp := pair_below x u v hu hv
    have hc : F (pair u v) (h' (pair u v)) = true := by
      rw [hpairs u v huv, hcorrect, pair_target G u v huv]
    exact hF (pair u v) x hp _ _ (hmono _ _ hp) hc

def star {n : ℕ} (a b c : Fin n) (x : Fin n → Bool) : Bool :=
  x c && (x a || x b)

def cleanStar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (b c : Fin n) (x : Fin n → Bool) : Bool :=
  if G.Adj c b then x c && x b else false

lemma cleanStar_positive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (b c : Fin n) : Positive (cleanStar G b c) := by
  intro x y hxy hx
  by_cases hcb : G.Adj c b
  · simp only [cleanStar, if_pos hcb, Bool.and_eq_true] at hx ⊢
    exact ⟨hxy c hx.1, hxy b hx.2⟩
  · simp [cleanStar, hcb] at hx

lemma cleanStar_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) : Below (cleanStar G b c) (star a b c) := by
  intro x hx
  by_cases hcb : G.Adj c b
  · simp only [cleanStar, if_pos hcb, Bool.and_eq_true] at hx
    simp [star, hx.1, hx.2]
  · simp [cleanStar, hcb] at hx

lemma pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) (u v c d : Fin n)
    (huv : G.Adj u v) (hcd : c ≠ d)
    (hc : pair u v c = true) (hd : pair u v d = true) : G.Adj c d := by
  simp only [pair, decide_eq_true_eq] at hc hd
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · exact (hcd rfl).elim
  · exact huv
  · exact G.adj_symm huv
  · exact (hcd rfl).elim

lemma cleanStar_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (hca : c ≠ a) (hcb : c ≠ b) (hbad : ¬ G.Adj c a) :
    ∀ u v, G.Adj u v → cleanStar G b c (pair u v) = star a b c (pair u v) := by
  intro u v huv
  cases hs : star a b c (pair u v) with
  | false =>
    cases hh : cleanStar G b c (pair u v) with
    | false => rfl
    | true =>
      have h := cleanStar_below G a b c _ hh
      rw [hs] at h
      contradiction
  | true =>
    have hs' := hs
    simp only [star, Bool.and_eq_true, Bool.or_eq_true] at hs'
    rcases hs'.2 with ha | hb
    · exact (hbad (pair_adj G u v c a huv hca hs'.1 ha)).elim
    · have hadj := pair_adj G u v c b huv hcb hs'.1 hb
      simp [cleanStar, hadj, hs'.1, hb]

def Run (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

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
    {xs ys : List Bool} (h : ListBelow xs ys) : ListBelow (Run gs xs) (Run gs ys) := by
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

def continuation {n : ℕ} (a b : Fin n) (gs : List Gate) (out : ℕ)
    (x : Fin n → Bool) (h : Bool) : Bool :=
  (Run gs (List.ofFn x ++ [x a || x b, h])).getD out false

lemma continuation_positive {n : ℕ} (a b : Fin n) (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ x y, (∀ i, x i = true → y i = true) →
      ∀ s t, (s = true → t = true) →
        continuation a b gs out x s = true → continuation a b gs out y t = true := by
  intro x y hxy s t hst
  have hab : (x a || x b) = true → (y a || y b) = true := by
    simp only [Bool.or_eq_true]
    exact fun h => h.elim (fun ha => Or.inl (hxy a ha)) (fun hb => Or.inr (hxy b hb))
  have h := run_mono gs hg (snoc_below (snoc_below (ofFn_below x y hxy) hab) hst)
  simpa only [continuation, List.append_assoc, List.singleton_append, List.nil_append] using h.2 out

theorem two_gate_star_cleaning {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (hca : c ≠ a) (hcb : c ≠ b) (hbad : ¬ G.Adj c a)
    (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x, continuation a b gs out x (star a b c x) = target G x) :
    ∀ x, continuation a b gs out x (cleanStar G b c x) = target G x := by
  exact minterm_replacement G (continuation a b gs out) (star a b c) (cleanStar G b c)
    (continuation_positive a b gs out hg) (cleanStar_positive G b c)
    (cleanStar_below G a b c) (cleanStar_pairs G a b c hca hcb hbad) hcorrect

def original {n : ℕ} (a b c : Fin n) (gs : List Gate) (out : ℕ) : Circuit :=
  ⟨⟨GateOp.or, [a, b]⟩ :: ⟨GateOp.and, [c, n]⟩ :: gs, out⟩

def cleaned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (gs : List Gate) (out : ℕ) : Circuit :=
  ⟨⟨GateOp.or, [a, b]⟩ ::
    (if G.Adj c b then ⟨GateOp.and, [c, b]⟩ else ⟨GateOp.or, []⟩) :: gs, out⟩

lemma read_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma read_ofFn_snoc {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    (List.ofFn x ++ [b]).getD i false = x i := by
  rw [List.getD_append _ _ _ _ (by simp), read_ofFn]

lemma read_ofFn_last {n : ℕ} (x : Fin n → Bool) (b : Bool) :
    (List.ofFn x ++ [b]).getD n false = b := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma original_eval {n : ℕ} (a b c : Fin n) (gs : List Gate) (out : ℕ)
    (x : Fin n → Bool) :
    (original a b c gs out).eval (List.ofFn x) =
      continuation a b gs out x (star a b c x) := by
  simp only [original, Circuit.eval, Circuit.wires, List.foldl_cons,
    GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true,
    read_ofFn, read_ofFn_snoc, read_ofFn_last]
  simp only [continuation, Run, GateOp.eval, star, List.append_assoc, List.singleton_append, List.nil_append]

lemma cleaned_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    (cleaned G a b c gs out).eval (List.ofFn x) =
      continuation a b gs out x (cleanStar G b c x) := by
  by_cases hcb : G.Adj c b
  · simp only [cleaned, if_pos hcb, Circuit.eval, Circuit.wires, List.foldl_cons,
      GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true,
      read_ofFn, read_ofFn_snoc, cleanStar, if_pos hcb]
    simp only [continuation, Run, GateOp.eval, List.append_assoc, List.singleton_append, List.nil_append]
  · simp only [cleaned, if_neg hcb, Circuit.eval, Circuit.wires, List.foldl_cons,
      GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, read_ofFn, cleanStar, if_neg hcb]
    simp only [continuation, Run, GateOp.eval, List.append_assoc, List.singleton_append, List.nil_append]

theorem same_size_circuit_cleaning {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (hca : c ≠ a) (hcb : c ≠ b) (hbad : ¬ G.Adj c a)
    (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x, (original a b c gs out).eval (List.ofFn x) = target G x) :
    (cleaned G a b c gs out).size = (original a b c gs out).size ∧
    PEqualNP.MetaComplexity.Monotone2 (cleaned G a b c gs out) ∧
    ∀ x, (cleaned G a b c gs out).eval (List.ofFn x) = target G x := by
  refine ⟨rfl, ?_, ?_⟩
  · intro g hmem
    simp only [cleaned, List.mem_cons] at hmem
    rcases hmem with rfl | rfl | hmem
    · simp
    · split_ifs <;> simp
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg g hmem
  · intro x
    rw [cleaned_eval]
    apply two_gate_star_cleaning G a b c hca hcb hbad gs out
      (fun g hg' => (hg g hg').1)
    intro y
    simpa only [original_eval] using hcorrect y

theorem every_wire_decreases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (x : Fin n → Bool) (w : ℕ), ((cleaned G a b c gs out).wires (List.ofFn x)).getD w false = true →
      ((original a b c gs out).wires (List.ofFn x)).getD w false = true := by
  intro x w
  change (cleaned G a b c gs w).eval (List.ofFn x) = true →
    (original a b c gs w).eval (List.ofFn x) = true
  rw [cleaned_eval, original_eval]
  exact continuation_positive a b gs w hg x x (fun _ hi => hi) _ _
    (cleanStar_below G a b c x)

def pathTarget (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)

def earlyWires (x : Fin 4 → Bool) : Fin 6 → Bool :=
  ![x 0, x 1, x 2, x 3, x 0 || x 1, x 2 || x 3]

def binary (isAnd : Bool) (a b : Bool) : Bool :=
  if isAnd then a && b else a || b

theorem dirty_rectangle_can_be_filtered : ∀ x : Fin 4 → Bool,
    (((x 0 || x 1) && (x 2 || x 3)) && (x 0 || x 2)) = pathTarget x := by
  decide +kernel

theorem clean_path_four_gate_expression : ∀ x : Fin 4 → Bool,
    ((x 0 && (x 2 || x 3)) || (x 1 && x 2)) = pathTarget x := by
  decide +kernel

theorem rectangle_cleaning_needs_more_than_one_available_gate :
    ∀ i j : Fin 6, ∀ isAnd : Bool,
      ¬ ∀ x : Fin 4 → Bool, binary isAnd (earlyWires x i) (earlyWires x j) = pathTarget x := by
  decide +kernel

def negativeActivations {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (C : Circuit) : Finset ((Fin n → Bool) × Fin (n + k)) :=
  Finset.univ.filter fun p => target G p.1 = false ∧
    (C.wires (List.ofFn p.1)).getD p.2 false = true

def dirt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (C : Circuit) : ℕ := (negativeActivations G k C).card

lemma dirt_strict_of_down {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit)
    (hdown : ∀ (x : Fin n → Bool) (i : ℕ),
      (D.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn x)).getD i false = true)
    (x : Fin n → Bool) (i : Fin (n + k)) (hx : target G x = false)
    (hC : (C.wires (List.ofFn x)).getD i false = true)
    (hD : (D.wires (List.ofFn x)).getD i false = false) :
    dirt G k D < dirt G k C := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro p hp
    simp only [negativeActivations, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, hdown p.1 p.2 hp.2⟩
  · intro heq
    have hp : (x, i) ∈ negativeActivations G k C := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hC⟩
    rw [← heq] at hp
    have ht := (Finset.mem_filter.mp hp).2.2
    rw [hD] at ht
    contradiction

lemma run_preserves_prefix (gs : List Gate) (xs : List Bool) (i : ℕ)
    (hi : i < xs.length) : (Run gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (Run gs (xs ++ [_])).getD i false = xs.getD i false
    rw [ih _ (by simpa using Nat.lt_succ_of_lt hi), List.getD_append _ _ _ _ hi]

lemma continuation_second_wire {n : ℕ} (a b : Fin n) (gs : List Gate)
    (x : Fin n → Bool) (h : Bool) : continuation a b gs (n + 1) x h = h := by
  unfold continuation
  rw [run_preserves_prefix _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma nonedge_pair_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a c : Fin n) (hbad : ¬ G.Adj c a) : target G (pair c a) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [target, decide_eq_true_eq] at h
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [pair, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact G.ne_of_adj huv rfl
  · exact hbad huv
  · exact hbad (G.adj_symm huv)
  · exact G.ne_of_adj huv rfl

lemma cleanStar_nonedge_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (hcb : c ≠ b) (hbad : ¬ G.Adj c a) :
    cleanStar G b c (pair c a) = false := by
  by_cases hba : b = a
  · subst b
    simp [cleanStar, hbad]
  · simp [cleanStar, pair, Ne.symm hcb, hba]

theorem early_star_strictly_reduces_dirt {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (hcb : c ≠ b) (hbad : ¬ G.Adj c a)
    (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    dirt G (gs.length + 2) (cleaned G a b c gs out) <
      dirt G (gs.length + 2) (original a b c gs out) := by
  apply dirt_strict_of_down G _ _ (every_wire_decreases G a b c gs out hg)
    (pair c a) ⟨n + 1, by omega⟩ (nonedge_pair_false G a c hbad)
  · change (original a b c gs (n + 1)).eval (List.ofFn (pair c a)) = true
    rw [original_eval, continuation_second_wire]
    simp [star, pair]
  · change (cleaned G a b c gs (n + 1)).eval (List.ofFn (pair c a)) = false
    rw [cleaned_eval, continuation_second_wire]
    exact cleanStar_nonedge_pair G a b c hcb hbad

theorem exists_least_dirt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hc : ∀ x, C.eval (List.ofFn x) = target G x) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size ∧
      (∀ x, D.eval (List.ofFn x) = target G x) ∧
      ∀ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E → E.size = C.size →
        (∀ x, E.eval (List.ofFn x) = target G x) → dirt G C.size D ≤ dirt G C.size E := by
  classical
  have hex : ∃ m : ℕ, ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size = C.size ∧ (∀ x, D.eval (List.ofFn x) = target G x) ∧ dirt G C.size D = m :=
    ⟨dirt G C.size C, C, hmono, rfl, hc, rfl⟩
  obtain ⟨D, hD, hsize, hcorrect, hd⟩ := Nat.find_spec hex
  refine ⟨D, hD, hsize, hcorrect, ?_⟩
  intro E hE hEs hEc
  rw [hd]
  exact Nat.find_min' hex ⟨E, hE, hEs, hEc, rfl⟩

theorem least_dirt_forces_first_star_edge {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (hca : c ≠ a) (hcb : c ≠ b)
    (gs : List Gate) (out : ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 (original a b c gs out))
    (hc : ∀ x, (original a b c gs out).eval (List.ofFn x) = target G x)
    (hmin : ∀ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E →
      E.size = (original a b c gs out).size →
      (∀ x, E.eval (List.ofFn x) = target G x) →
      dirt G (original a b c gs out).size (original a b c gs out) ≤
        dirt G (original a b c gs out).size E) : G.Adj c a := by
  by_contra hbad
  have hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hmem
    have h := hmono g (by simp [original, hmem])
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  obtain ⟨hsize, hm, hcorrect⟩ := same_size_circuit_cleaning G a b c hca hcb hbad gs out hg hc
  have hle := hmin (cleaned G a b c gs out) hm hsize hcorrect
  have hlt := early_star_strictly_reduces_dirt G a b c hcb hbad gs out (fun g h => (hg g h).1)
  have hs : (original a b c gs out).size = gs.length + 2 := by simp [original, Circuit.size]
  rw [hs] at hle
  omega

lemma original_eval_swap {n : ℕ} (a b c : Fin n) (gs : List Gate) (out : ℕ)
    (x : Fin n → Bool) : (original a b c gs out).eval (List.ofFn x) =
      (original b a c gs out).eval (List.ofFn x) := by
  rw [original_eval, original_eval]
  simp only [continuation, star, Bool.or_comm (x a) (x b)]

lemma dirt_original_swap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (a b c : Fin n) (gs : List Gate) (out : ℕ) :
    dirt G k (original a b c gs out) = dirt G k (original b a c gs out) := by
  unfold dirt
  congr 1
  ext p
  simp only [negativeActivations, Finset.mem_filter, Finset.mem_univ, true_and]
  have h : ((original a b c gs out).wires (List.ofFn p.1)).getD p.2 false =
      ((original b a c gs out).wires (List.ofFn p.1)).getD p.2 false :=
    original_eval_swap a b c gs p.2 p.1
  rw [h]

theorem least_dirt_forces_both_star_edges {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (hca : c ≠ a) (hcb : c ≠ b)
    (gs : List Gate) (out : ℕ)
    (hmono : PEqualNP.MetaComplexity.Monotone2 (original a b c gs out))
    (hc : ∀ x, (original a b c gs out).eval (List.ofFn x) = target G x)
    (hmin : ∀ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E →
      E.size = (original a b c gs out).size →
      (∀ x, E.eval (List.ofFn x) = target G x) →
      dirt G (original a b c gs out).size (original a b c gs out) ≤
        dirt G (original a b c gs out).size E) : G.Adj c a ∧ G.Adj c b := by
  refine ⟨least_dirt_forces_first_star_edge G a b c hca hcb gs out hmono hc hmin, ?_⟩
  apply least_dirt_forces_first_star_edge G b a c hcb hca gs out
  · intro g hg
    simp only [original, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact hmono g (by simp [original, hg])
  · intro x
    rw [← original_eval_swap a b c gs out x]
    exact hc x
  · intro E hE hs hEc
    have h := hmin E hE hs hEc
    rw [dirt_original_swap G _ a b c gs out] at h
    exact h

theorem exists_early_star_normal_form {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hc : ∀ x, C.eval (List.ofFn x) = target G x) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size ∧
      (∀ x, D.eval (List.ofFn x) = target G x) ∧
      ∀ (a b c : Fin n), c ≠ a → c ≠ b → ∀ (gs : List Gate) (out : ℕ),
        D = original a b c gs out → G.Adj c a ∧ G.Adj c b := by
  obtain ⟨D, hm, hs, hcD, hmin⟩ := exists_least_dirt G C hmono hc
  refine ⟨D, hm, hs, hcD, ?_⟩
  intro a b c hca hcb gs out hD
  subst D
  apply least_dirt_forces_both_star_edges G a b c hca hcb gs out hm hcD
  intro E hE hEs hEc
  simpa only [hs] using hmin E hE (hEs.trans hs) hEc

end PEqualNP.Outside.PairCleaning
