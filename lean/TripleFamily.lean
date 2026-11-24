import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LinearTripleFamily

-- The two-private-gate argument generalizes the checked L-meta-1042 proof.
-- Circuit semantics and the basic argument follow that Apache-2.0 source.

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj



variable {n m : ℕ}

def Inc (point : Fin m → Fin 3 → Fin n) (l : Fin m) (p : Fin n) : Prop :=
  ∃ c : Fin 3, p = point l c

def hit (point : Fin m → Fin 3 → Fin n) (l : Fin m) (x : Fin n → Bool) : Prop :=
  ∃ c : Fin 3, x (point l c) = true

def single (p : Fin n) : Fin n → Bool := fun k => decide (k = p)

def outside (point : Fin m → Fin 3 → Fin n) (l : Fin m) : Fin n → Bool :=
  fun k => decide (¬ Inc point l k)

variable {point : Fin m → Fin 3 → Fin n}

lemma same_line
    (hsep : ∀ (l r : Fin m) (c d : Fin 3), c ≠ d →
      Inc point r (point l c) → Inc point r (point l d) → l = r)
    (l r : Fin m) (c d : Fin 3) (hcd : c ≠ d)
    (hc : Inc point r (point l c)) (hd : Inc point r (point l d)) : l = r :=
  hsep l r c d hcd hc hd

lemma different_points (hinj : ∀ l, Function.Injective (point l))
    (l : Fin m) (c d : Fin 3) (h : c ≠ d) : point l c ≠ point l d :=
  fun he => h (hinj l he)

lemma hit_single (l : (Fin m)) (p : Fin n) : hit point l (single p) ↔ Inc point l p := by
  simp [hit, Inc, single, eq_comm]

lemma hit_point (l : (Fin m)) (c : Fin 3) : hit point l (single (point l c)) :=
  (hit_single _ _).2 ⟨c, rfl⟩

lemma miss (l : (Fin m)) : ¬ hit point l (outside point l) := by
  rintro ⟨c, hc⟩
  exact (of_decide_eq_true hc) ⟨c, rfl⟩

def Low (point : Fin m → Fin 3 → Fin n) (l : (Fin m)) (f : ((Fin n → Bool) → Bool)) := ∀ x, f x = true → hit point l x
def High (point : Fin m → Fin 3 → Fin n) (l : (Fin m)) (f : ((Fin n → Bool) → Bool)) := ∀ x, hit point l x → f x = true
def Exact (point : Fin m → Fin 3 → Fin n) (l : (Fin m)) (f : ((Fin n → Bool) → Bool)) := ∀ x, f x = true ↔ hit point l x

def Good (point : Fin m → Fin 3 → Fin n) (l : (Fin m)) (f : ((Fin n → Bool) → Bool)) :=
  (Low point l f ∨ High point l f) ∧
  (∃ c d : Fin 3, c ≠ d ∧ f (single (point l c)) = true ∧ f (single (point l d)) = true) ∧
  f (outside point l) = false

lemma exact_good {l : (Fin m)} {f : ((Fin n → Bool) → Bool)} (h : Exact point l f) : Good point l f :=
  ⟨Or.inl (fun x => (h x).1),
    ⟨0, 1, by decide, (h _).2 (hit_point _ _), (h _).2 (hit_point _ _)⟩,
    Bool.eq_false_iff.mpr (fun ht => miss l ((h _).1 ht))⟩

lemma unique_line (hsep : ∀ (l r : Fin m) (c d : Fin 3), c ≠ d →
      Inc point r (point l c) → Inc point r (point l d) → l = r) {l m : (Fin m)} {f : ((Fin n → Bool) → Bool)} (h : Good point l f) (h' : Good point m f) : l = m := by
  obtain ⟨_, ⟨c, d, hn, hc, hd⟩, hf⟩ := h
  rcases h'.1 with low | high
  · apply same_line hsep l m c d hn
    · exact (hit_single _ _).1 (low _ hc)
    · exact (hit_single _ _).1 (low _ hd)
  · have inc (j : Fin 3) : Inc point l (point m j) := by
      by_contra hh
      have ht := high (outside point l) ⟨j, by simpa [outside point] using hh⟩
      simp [hf] at ht
    exact (same_line hsep m l 0 1 (by decide) (inc _) (inc _)).symm

def Falls (f : ((Fin n → Bool) → Bool)) := ∀ x y : (Fin n → Bool), (∀ k, x k = true → y k = true) →
  f y = true → f x = true

lemma good_rises {l : (Fin m)} {f : ((Fin n → Bool) → Bool)} (h : Good point l f) : ¬ Falls f := by
  rintro hf
  obtain ⟨hl | hh, ⟨c, _, _, hc, _⟩, ho⟩ := h
  · have h0 := hf (fun _ => false) _ (by simp) hc
    obtain ⟨_, hn⟩ := hl _ h0
    contradiction
  · have h1 := hh (fun _ => true) ⟨0, rfl⟩
    have ht := hf (outside point l) (fun _ => true) (by simp) h1
    simp [ho] at ht

lemma good_or {l : (Fin m)} {u v : ((Fin n → Bool) → Bool)}
    (he : Exact point l (fun x => u x || v x)) : Good point l u ∨ Good point l v := by
  have lu : Low point l u := fun x h => (he x).1 (by simp [h])
  have lv : Low point l v := fun x h => (he x).1 (by simp [h])
  have fu : u (outside point l) = false := Bool.eq_false_iff.mpr (fun h => miss l (lu _ h))
  have fv : v (outside point l) = false := Bool.eq_false_iff.mpr (fun h => miss l (lv _ h))
  have cov (c : Fin 3) := (he _).2 (hit_point l c)
  simp only [Bool.or_eq_true] at cov
  have gu (c d : Fin 3) (hn : c ≠ d) (hc : u (single (point l c)) = true)
      (hd : u (single (point l d)) = true) : Good point l u ∨ Good point l v :=
    Or.inl ⟨Or.inl lu, ⟨c, d, hn, hc, hd⟩, fu⟩
  have gv (c d : Fin 3) (hn : c ≠ d) (hc : v (single (point l c)) = true)
      (hd : v (single (point l d)) = true) : Good point l u ∨ Good point l v :=
    Or.inr ⟨Or.inl lv, ⟨c, d, hn, hc, hd⟩, fv⟩
  rcases cov 0 with a | a <;> rcases cov 1 with b | b <;> rcases cov 2 with c | c
  all_goals first
    | exact gu 0 1 (by decide) a b
    | exact gu 0 2 (by decide) a c
    | exact gu 1 2 (by decide) b c
    | exact gv 0 1 (by decide) a b
    | exact gv 0 2 (by decide) a c
    | exact gv 1 2 (by decide) b c

lemma good_and {l : (Fin m)} {u v : ((Fin n → Bool) → Bool)}
    (he : Exact point l (fun x => u x && v x)) : Good point l u ∨ Good point l v := by
  have hh (x : (Fin n → Bool)) (h : hit point l x) : u x = true ∧ v x = true := by
    have ht := (he x).2 h
    simpa only [Bool.and_eq_true] using ht
  have makeGood (f : ((Fin n → Bool) → Bool)) (h : High point l f) (hf : f (outside point l) = false) : Good point l f :=
    ⟨Or.inr h, ⟨0, 1, by decide, h _ (hit_point _ _), h _ (hit_point _ _)⟩, hf⟩
  cases hu : u (outside point l) with
  | false => exact Or.inl (makeGood _ (fun x h => (hh x h).1) hu)
  | true =>
    apply Or.inr (makeGood _ (fun x h => (hh x h).2) _)
    apply Bool.eq_false_iff.mpr
    intro hv
    exact miss l ((he _).1 (by simp [hu, hv]))

def wire (gs : List Gate) (i : ℕ) (x : (Fin n → Bool)) :=
  (wiresFrom gs (List.ofFn x)).getD i false

def prior (gs : List Gate) (k i : ℕ) : ((Fin n → Bool) → Bool) :=
  if i < n + k then wire gs i else fun _ => false

lemma prior_apply (gs : List Gate) (k i : ℕ) (x : (Fin n → Bool)) :
    prior gs k i x = if i < n+k then wire gs i x else false := by
  by_cases h : i < n+k <;> simp [prior, h]

lemma wire_gate (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : (Fin n → Bool)) :
    wire gs (n+k) x = gs[k].op.eval (gs[k].inputs.map (fun i => prior gs k i x)) := by
  simpa only [prior_apply, wire, List.length_ofFn] using getD_wiresFrom_gate gs (List.ofFn x) k hk

lemma good_in_range (hinj : ∀ l, Function.Injective (point l)) {gs : List Gate} {i : ℕ} {l : (Fin m)} (h : Good point l (wire gs i)) :
    n ≤ i ∧ i < n + gs.length := by
  obtain ⟨_, ⟨c, d, hn, hc, hd⟩, _⟩ := h
  constructor
  · by_contra! hi
    have inp (x : (Fin n → Bool)) : wire gs i x = x ⟨i, hi⟩ := by
      unfold wire
      rw [getD_wiresFrom_lt _ _ _ (by simpa)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] : i < (List.ofFn x).length), List.getElem_ofFn]
    rw [inp] at hc hd
    exact different_points hinj l c d hn ((of_decide_eq_true hc).symm.trans (of_decide_eq_true hd))
  · by_contra! hi
    unfold wire at hc
    rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using hi)] at hc
    contradiction

lemma from_prior {gs : List Gate} {k i : ℕ} {l : (Fin m)} (h : Good point l (prior gs k i)) :
    ∃ j < n+k, Good point l (wire gs j) := by
  unfold prior at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · exact False.elim (good_rises h (fun _ _ _ ht => ht))


def OnlyOne (C : Circuit) := ∀ i j : Fin C.gates.length,
  (C.gates.get i).op = GateOp.not → (C.gates.get j).op = GateOp.not → i = j

lemma not_falls (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (k : ℕ) (hk : k < C.gates.length) (hop : C.gates[k].op = GateOp.not) :
    Falls (wire C.gates (n+k)) := by
  have hm : ∀ g ∈ C.gates.take k, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hik : i < k := by simp only [List.length_take] at hi; omega
    have hil : i < C.gates.length := by omega
    rw [List.getElem_take]
    have hg' := (hf C.gates[i] (List.getElem_mem hil)).1
    rcases hg' with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have he := hu ⟨i, hil⟩ ⟨k, hk⟩ h hop
      have he' : i = k := congrArg Fin.val he
      omega
  intro x y hxy
  have hle (i : ℕ) : prior C.gates k i x = true → prior C.gates k i y = true := by
    have hv (z : (Fin n → Bool)) : prior C.gates k i z =
        (wiresFrom (C.gates.take k) (List.ofFn z)).getD i false := by
      rw [getD_wiresFrom_take _ _ _ _ (by omega)]
      simp only [prior_apply, wire, List.length_ofFn]
    rw [hv, hv]
    apply wiresFrom_mono _ hm _ _ (by simp)
    intro t ht
    by_cases h : t < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at ht ⊢
      simp only [List.getElem_ofFn] at ht ⊢
      exact hxy ⟨t,h⟩ ht
    · rw [List.getD_eq_default _ _ (by simp; omega)] at ht
      contradiction
  rw [wire_gate _ _ hk, wire_gate _ _ hk, hop]
  cases he : C.gates[k].inputs with
  | nil => simp [GateOp.eval]
  | cons i is =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_true']
    exact fun hy => Bool.eq_false_iff.mpr (fun hx => by simpa [hy] using hle i hx)

lemma earlier (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (l : (Fin m)) (k : ℕ) (hk : k < C.gates.length) (he : Exact point l (wire C.gates (n+k))) :
    ∃ i < n+k, Good point l (wire C.gates i) := by
  let g := C.gates[k]
  have ha := hf g (List.getElem_mem hk)
  have leg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := ha.1
  have len := ha.2
  have eqn (x : (Fin n → Bool)) : wire C.gates (n+k) x =
      g.op.eval (g.inputs.map (fun i => prior C.gates k i x)) := wire_gate _ _ _ _
  have bad (b : Bool) (h : ∀ x, wire C.gates (n+k) x = b) : False := by
    apply good_rises (exact_good he)
    intro x y _ ht
    rwa [h x, ← h y]
  rcases leg with ha | ho | hn
  · cases hin : g.inputs with
    | nil => exact (bad true (by simp [eqn, hin, ha, GateOp.eval])).elim
    | cons i rest =>
      cases rest with
      | nil =>
        apply from_prior (i := i)
        apply exact_good
        intro x
        simpa [eqn, hin, ha, GateOp.eval] using he x
      | cons j more =>
        have em : more = [] := by rw [hin] at len; simpa using len
        rw [em] at hin
        have h : Exact point l (fun x => prior C.gates k i x && prior C.gates k j x) := by
          intro x
          simpa [eqn, hin, ha, GateOp.eval] using he x
        exact (good_and h).elim from_prior from_prior
  · cases hin : g.inputs with
    | nil => exact (bad false (by simp [eqn, hin, ho, GateOp.eval])).elim
    | cons i rest =>
      cases rest with
      | nil =>
        apply from_prior (i := i)
        apply exact_good
        intro x
        simpa [eqn, hin, ho, GateOp.eval] using he x
      | cons j more =>
        have em : more = [] := by rw [hin] at len; simpa using len
        rw [em] at hin
        have h : Exact point l (fun x => prior C.gates k i x || prior C.gates k j x) := by
          intro x
          simpa [eqn, hin, ho, GateOp.eval] using he x
        exact (good_or h).elim from_prior from_prior
  · exact (good_rises (exact_good he) (not_falls C hf hu k hk hn)).elim


lemma pair_gates (hinj : ∀ l, Function.Injective (point l)) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (l : (Fin m)) (o : ℕ) (he : Exact point l (wire C.gates o)) :
    ∃ i j : Fin C.gates.length, i ≠ j ∧
      Good point l (wire C.gates (n+i.val)) ∧ Good point l (wire C.gates (n+j.val)) := by
  have hg := exact_good he
  obtain ⟨ho, ho'⟩ := good_in_range hinj hg
  let j : Fin C.gates.length := ⟨o-n, by omega⟩
  have hj : n + j.val = o := by dsimp [j]; omega
  obtain ⟨p, hp, hgp⟩ := earlier C hf hu l j j.isLt (hj ▸ he)
  obtain ⟨hp0, hp1⟩ := good_in_range hinj hgp
  let i : Fin C.gates.length := ⟨p-n, by omega⟩
  have hi : n + i.val = p := by dsimp [i]; omega
  refine ⟨i, j, ?_, hi ▸ hgp, hj ▸ hg⟩
  intro eqij
  rw [← eqij, hi] at hp
  omega

theorem count_gates (hinj : ∀ l, Function.Injective (point l)) (hsep : ∀ (l r : Fin m) (c d : Fin 3), c ≠ d →
      Inc point r (point l c) → Inc point r (point l d) → l = r) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (he : ∀ l : (Fin m), ∃ o : ℕ, Exact point l (wire C.gates o)) :
    2 * m ≤ C.gates.length := by
  classical
  choose o hout using he
  choose i j hne hi hj using fun l => pair_gates hinj C hf hu l (o l) (hout l)
  let idx (p : (Fin m) × Bool) := if p.2 then i p.1 else j p.1
  have good (p : (Fin m) × Bool) : Good point p.1 (wire C.gates (n+(idx p).val)) := by
    rcases p with ⟨l, b⟩
    cases b
    · exact hj l
    · exact hi l
  have hinj : Function.Injective idx := by
    rintro ⟨l, b⟩ ⟨m, d⟩ h
    have h1 := good (l, b)
    rw [h] at h1
    have hl : l = m := unique_line hsep h1 (good (m, d))
    subst m
    cases b <;> cases d
    · rfl
    · exact (hne l h.symm).elim
    · exact (hne l h).elim
    · rfl
  have hc : Fintype.card ((Fin m) × Bool) = m * 2 := by simp
  have hle := Fintype.card_le_of_injective _ hinj
  simpa only [hc, Fintype.card_fin, Nat.mul_comm] using hle


end PEqualNP.Outside.LinearTripleFamily
