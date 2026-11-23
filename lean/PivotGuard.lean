import Mathlib

namespace PEqualNP.Outside.PivotGuard

abbrev Input (N : ℕ) := (Fin N → Bool) × (Fin N → Bool)

def Above {N : ℕ} (z z' : Input N) :=
  (∀ p, z.1 p = true → z'.1 p = true) ∧ (∀ l, z.2 l = true → z'.2 l = true)

def Positive {N : ℕ} (F : Input N → Bool) :=
  ∀ z z', Above z z' → F z = true → F z' = true

def Edge {N : ℕ} (I : Fin N → Fin N → Prop) (z : Input N) :=
  ∃ p l, I p l ∧ z.1 p = true ∧ z.2 l = true

def lineOnly {N : ℕ} (u : Fin N) : Input N :=
  (fun _ => false, fun l => decide (l = u))

def raiseLine {N : ℕ} (z : Input N) (u : Fin N) : Input N :=
  (z.1, fun l => z.2 l || decide (l = u))

lemma above_raise {N : ℕ} (z : Input N) (u : Fin N) : Above z (raiseLine z u) := by
  constructor
  · exact fun _ hp => hp
  · intro l hl
    simp [raiseLine, hl]

lemma line_below_raise {N : ℕ} (z : Input N) (u : Fin N) :
    Above (lineOnly u) (raiseLine z u) := by
  constructor
  · simp [lineOnly]
  · intro l hl
    have hu : l = u := of_decide_eq_true hl
    simp [raiseLine, hu]

lemma remove_guard_edge {N : ℕ} (I : Fin N → Fin N → Prop) (z : Input N) (u : Fin N)
    (hmiss : ∀ p, I p u → z.1 p = false) : Edge I (raiseLine z u) → Edge I z := by
  rintro ⟨p, l, hI, hp, hl⟩
  have hy : z.2 l = true ∨ l = u := by
    simpa [raiseLine] using hl
  rcases hy with hy | rfl
  · exact ⟨p, l, hI, hp, hy⟩
  · have hz := hmiss p hI
    have ht : z.1 p = true := hp
    simp [hz] at ht

-- A line accepted by the second factor can serve as a pivot for the first.
theorem factor_is_sound_off_pivot {N : ℕ} (I : Fin N → Fin N → Prop)
    (A B : Input N → Bool) (ha : Positive A) (hb : Positive B)
    (hsound : ∀ z, A z = true → B z = true → Edge I z)
    (u : Fin N) (hu : B (lineOnly u) = true) :
    ∀ z, (∀ p, I p u → z.1 p = false) → A z = true → Edge I z := by
  intro z hmiss haz
  apply remove_guard_edge I z u hmiss
  exact hsound (raiseLine z u)
    (ha z _ (above_raise z u) haz)
    (hb (lineOnly u) _ (line_below_raise z u) hu)

theorem factor_is_sound_off_pivot_set {N : ℕ} (I : Fin N → Fin N → Prop)
    (A B : Input N → Bool) (ha : Positive A) (hb : Positive B)
    (hsound : ∀ z, A z = true → B z = true → Edge I z)
    (W : Finset (Fin N)) (hW : ∀ u ∈ W, B (lineOnly u) = true) :
    ∀ z, (∃ u ∈ W, ∀ p, I p u → z.1 p = false) → A z = true → Edge I z := by
  rintro z ⟨u, hu, hmiss⟩ haz
  exact factor_is_sound_off_pivot I A B ha hb hsound u (hW u hu) z hmiss haz

end PEqualNP.Outside.PivotGuard
