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
  · exact G.symm huv
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
  have hab : x a || x b = true → y a || y b = true := by
    simp only [Bool.or_eq_true]
    exact fun h => h.elim (fun ha => Or.inl (hxy a ha)) (fun hb => Or.inr (hxy b hb))
  have h := run_mono gs hg (snoc_below (snoc_below (ofFn_below x y hxy) hab) hst)
  simpa only [List.append_assoc, List.singleton_append, List.nil_append] using h.2 out

theorem two_gate_star_cleaning {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c : Fin n) (hca : c ≠ a) (hcb : c ≠ b) (hbad : ¬ G.Adj c a)
    (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x, continuation a b gs out x (star a b c x) = target G x) :
    ∀ x, continuation a b gs out x (cleanStar G b c x) = target G x := by
  exact minterm_replacement G (continuation a b gs out) (star a b c) (cleanStar G b c)
    (continuation_positive a b gs out hg) (cleanStar_positive G b c)
    (cleanStar_below G a b c) (cleanStar_pairs G a b c hca hcb hbad) hcorrect

end PEqualNP.Outside.PairCleaning
