import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.BoundedDegreeDiagonal

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases he : i = w.length
  · subst i
    simp
  · by_cases hi : i < w.length
    · simp [he, List.getD_append _ _ _ _ hi]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]
      simp [he]

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

def used (gs : List Gate) : Finset ℕ := (gs.flatMap Gate.inputs).toFinset

lemma used_card (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (used gs).card ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [used]
  | cons g gs ih =>
    have hsplit : used (g :: gs) = g.inputs.toFinset ∪ used gs := by simp [used]
    rw [hsplit]
    have h := Finset.card_union_le g.inputs.toFinset (used gs)
    have hc := List.toFinset_card_le g.inputs
    have hg := hf g List.mem_cons_self
    have ht := ih (fun g' hg' => hf g' (List.mem_cons_of_mem g hg'))
    simp only [List.length_cons]
    omega

def pair {N : ℕ} (p l : Fin N) : Fin (N+N) → Bool :=
  fun v => decide (v.val = p.val ∨ v.val = N + l.val)

def point {N : ℕ} (p : Fin N) : Fin (N+N) → Bool :=
  fun v => decide (v.val = p.val)

def line {N : ℕ} (l : Fin N) : Fin (N+N) → Bool :=
  fun v => decide (v.val = N + l.val)

lemma pair_line_agree {N : ℕ} (p l : Fin N) (i : ℕ) (hi : i ≠ p.val) :
    (List.ofFn (pair p l)).getD i false = (List.ofFn (line l)).getD i false := by
  by_cases hn : i < N+N
  · rw [List.getD_eq_getElem _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa)]
    simp [List.getElem_ofFn, pair, line, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma output_ne_point {N : ℕ} (gs : List Gate) (p : Fin N) (o : ℕ)
    (h : (wiresFrom gs (List.ofFn (point p))).getD o false = false) : o ≠ p.val := by
  intro he
  subst o
  rw [input_read _ _ _ (by simp; omega)] at h
  have hx : (List.ofFn (point p)).getD p.val false = true := by
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp [point]
  simp [hx] at h

-- Sound products cannot accept a point that no gate ever reads when both
-- factor outputs reject the point-only input.
theorem counted_point_is_used {N : ℕ} (gs : List Gate) (a b : ℕ) (p l : Fin N)
    (hs : ∀ z : Fin (N+N) → Bool,
      (wiresFrom gs (List.ofFn z)).getD a false = true →
      (wiresFrom gs (List.ofFn z)).getD b false = true →
      ∃ p' l' : Fin N, z (Fin.castAdd N p') = true ∧ z (Fin.natAdd N l') = true)
    (ha : (wiresFrom gs (List.ofFn (pair p l))).getD a false = true)
    (hb : (wiresFrom gs (List.ofFn (pair p l))).getD b false = true)
    (ha0 : (wiresFrom gs (List.ofFn (point p))).getD a false = false)
    (hb0 : (wiresFrom gs (List.ofFn (point p))).getD b false = false) :
    p.val ∈ used gs := by
  by_contra hnot
  have hu : ∀ g ∈ gs, p.val ∉ g.inputs := by
    intro g hg hp
    apply hnot
    simp only [used, List.mem_toFinset, List.mem_flatMap]
    exact ⟨g, hg, hp⟩
  have eqn := unused_preserves gs p.val hu (List.ofFn (pair p l)) (List.ofFn (line l))
    (by simp) (pair_line_agree p l)
  rw [eqn a (output_ne_point gs p a ha0)] at ha
  rw [eqn b (output_ne_point gs p b hb0)] at hb
  obtain ⟨p', l', hp', hl'⟩ := hs (line l) ha hb
  have he : p'.val = N + l.val := of_decide_eq_true hp'
  omega

theorem edge_count_of_used_points {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Gate) (E : Finset (Fin N × Fin N)) (D : ℕ)
    (hf : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hd : ∀ p, (Finset.univ.filter (fun l => I p l)).card ≤ D)
    (he : ∀ e ∈ E, I e.1 e.2 ∧ e.1.val ∈ used gs) :
    E.card ≤ 2 * D * gs.length := by
  classical
  let P := Finset.univ.filter (fun p : Fin N => p.val ∈ used gs)
  let row := fun p : Fin N => Finset.univ.filter (fun l => I p l)
  have hp : P.card ≤ (used gs).card := by
    have hsub : P.image Fin.val ⊆ used gs := by
      intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hp).2
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ Fin.val_injective] at hh
  have hsub : E ⊆ P.biUnion (fun p => {p} ×ˢ row p) := by
    intro e he'
    obtain ⟨hi, hu⟩ := he e he'
    apply Finset.mem_biUnion.mpr
    refine ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, ?_⟩
    simp [row, hi]
  have hcount := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hsum : (∑ p ∈ P, ({p} ×ˢ row p).card) ≤ P.card * D := by
    calc
      (∑ p ∈ P, ({p} ×ˢ row p).card) ≤ ∑ _p ∈ P, D := by
        apply Finset.sum_le_sum
        intro p hp
        simpa [row] using hd p
      _ = P.card * D := by simp
  have hc := used_card gs hf
  nlinarith

theorem diagonal_bound_degree_fifty {N J : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Gate) (fa fb : Fin J → ℕ) (E : Finset (Fin N × Fin N))
    (hf : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hd : ∀ p, (Finset.univ.filter (fun l => I p l)).card ≤ 50)
    (hs : ∀ (j : Fin J) (z : Fin (N+N) → Bool),
      (wiresFrom gs (List.ofFn z)).getD (fa j) false = true →
      (wiresFrom gs (List.ofFn z)).getD (fb j) false = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (he : ∀ e ∈ E, I e.1 e.2 ∧ ∃ j : Fin J,
      (wiresFrom gs (List.ofFn (pair e.1 e.2))).getD (fa j) false = true ∧
      (wiresFrom gs (List.ofFn (pair e.1 e.2))).getD (fb j) false = true ∧
      (wiresFrom gs (List.ofFn (point e.1))).getD (fa j) false = false ∧
      (wiresFrom gs (List.ofFn (point e.1))).getD (fb j) false = false) :
    E.card ≤ 100 * gs.length := by
  apply edge_count_of_used_points I gs E 50 hf hd
  intro e he'
  obtain ⟨hI, j, ha, hb, ha0, hb0⟩ := he e he'
  refine ⟨hI, counted_point_is_used gs (fa j) (fb j) e.1 e.2 ?_ ha hb ha0 hb0⟩
  intro z hz hz'
  obtain ⟨p, l, _, hp, hl⟩ := hs j z hz hz'
  exact ⟨p, l, hp, hl⟩

end PEqualNP.Outside.BoundedDegreeDiagonal
