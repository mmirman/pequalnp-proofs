import Mathlib

namespace PEqualNP.Outside.OneNotCofactors

abbrev Input (n : ℕ) := Fin n → Bool

def Above {n : ℕ} (x y : Input n) := ∀ i, x i = true → y i = true

def Positive {n : ℕ} (F : Input n → Bool → Bool) :=
  ∀ x y b c, Above x y → (b = true → c = true) → F x b = true → F y c = true

def target {n : ℕ} (S : Finset (Fin n)) (x : Input n) : Bool :=
  decide (∃ p ∈ S, x p = true)

def single {n : ℕ} (p : Fin n) : Input n := fun i => decide (i = p)

def outside {n : ℕ} (S : Finset (Fin n)) : Input n := fun i => decide (i ∉ S)

lemma target_single {n : ℕ} (S : Finset (Fin n)) (p : Fin n) :
    target S (single p) = decide (p ∈ S) := by
  simp [target, single]

lemma target_outside {n : ℕ} (S : Finset (Fin n)) :
    target S (outside S) = false := by
  simp [target, outside]

lemma lower_sound {n : ℕ} (S : Finset (Fin n)) (F : Input n → Bool → Bool)
    (h : Input n → Bool) (hm : Positive F)
    (hc : ∀ x, F x (Bool.not (h x)) = target S x) :
    ∀ x, F x false = true → target S x = true := by
  intro x hx
  rw [← hc x]
  exact hm x x false _ (fun _ hi => hi) (by simp) hx

lemma upper_complete {n : ℕ} (S : Finset (Fin n)) (F : Input n → Bool → Bool)
    (h : Input n → Bool) (hm : Positive F)
    (hc : ∀ x, F x (Bool.not (h x)) = target S x) :
    ∀ x, target S x = true → F x true = true := by
  intro x hx
  exact hm x x _ true (fun _ hi => hi) (by simp) ((hc x).trans hx)

-- All errors in the lower cofactor are witnessed by a singleton.
theorem lower_exact_iff {n : ℕ} (S : Finset (Fin n)) (F : Input n → Bool → Bool)
    (h : Input n → Bool) (hm : Positive F)
    (hc : ∀ x, F x (Bool.not (h x)) = target S x) :
    (∀ x, F x false = target S x) ↔ ∀ p ∈ S, F (single p) false = true := by
  constructor
  · intro he p hp
    rw [he, target_single, decide_eq_true hp]
  · intro hs x
    cases ht : target S x with
    | false =>
      apply Bool.eq_false_iff.mpr
      intro hf
      have := lower_sound S F h hm hc x hf
      simp [ht] at this
    | true =>
      obtain ⟨p, hp, hxp⟩ := of_decide_eq_true ht
      apply hm (single p) x false false _ (fun hb => hb) (hs p hp)
      intro i hi
      have hip : i = p := of_decide_eq_true hi
      simpa [hip] using hxp

-- All errors in the upper cofactor are witnessed by the complement of the line.
theorem upper_exact_iff {n : ℕ} (S : Finset (Fin n)) (F : Input n → Bool → Bool)
    (h : Input n → Bool) (hm : Positive F)
    (hc : ∀ x, F x (Bool.not (h x)) = target S x) :
    (∀ x, F x true = target S x) ↔ F (outside S) true = false := by
  constructor
  · intro he
    rw [he, target_outside]
  · intro ho x
    cases ht : target S x with
    | true => exact upper_complete S F h hm hc x ht
    | false =>
      apply Bool.eq_false_iff.mpr
      intro hf
      have hxy : Above x (outside S) := by
        intro p hp
        apply decide_eq_true
        intro hps
        have hit : target S x = true := decide_eq_true ⟨p, hps, hp⟩
        simp [ht] at hit
      have hout := hm x (outside S) true true hxy (fun hb => hb) hf
      simp [ho] at hout

theorem lower_failure_witness {n : ℕ} (S : Finset (Fin n))
    (F : Input n → Bool → Bool) (h : Input n → Bool) (hm : Positive F)
    (hc : ∀ x, F x (Bool.not (h x)) = target S x)
    (hf : ¬ ∀ x, F x false = target S x) :
    ∃ p ∈ S, h (single p) = false ∧ F (single p) false = false := by
  have hn : ¬ ∀ p ∈ S, F (single p) false = true :=
    fun hs => hf ((lower_exact_iff S F h hm hc).mpr hs)
  push_neg at hn
  obtain ⟨p, hp, hfp⟩ := hn
  refine ⟨p, hp, ?_, Bool.eq_false_iff.mpr hfp⟩
  cases hh : h (single p) with
  | false => rfl
  | true =>
    have he := hc (single p)
    simp only [hh, Bool.not_true, target_single, decide_eq_true hp] at he
    exact (hfp he).elim

theorem upper_failure_witness {n : ℕ} (S : Finset (Fin n))
    (F : Input n → Bool → Bool) (h : Input n → Bool) (hm : Positive F)
    (hc : ∀ x, F x (Bool.not (h x)) = target S x)
    (hf : ¬ ∀ x, F x true = target S x) :
    h (outside S) = true ∧ F (outside S) true = true := by
  have hn : F (outside S) true ≠ false :=
    fun ho => hf ((upper_exact_iff S F h hm hc).mpr ho)
  have ht : F (outside S) true = true := by
    cases he : F (outside S) true with
    | false => exact (hn he).elim
    | true => rfl
  refine ⟨?_, ht⟩
  cases hh : h (outside S) with
  | true => rfl
  | false =>
    have he := hc (outside S)
    simp only [hh, Bool.not_false, target_outside] at he
    exact (hn he).elim

end PEqualNP.Outside.OneNotCofactors
