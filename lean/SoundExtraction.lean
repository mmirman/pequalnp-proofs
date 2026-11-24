import Mathlib

namespace PEqualNP.Outside.SoundExtraction

-- Pulling a sound signal to the output does not require positivity.
theorem extract {X : Type} (F : X → Bool → Bool) (h f : X → Bool)
    (hcorrect : ∀ x, F x (h x) = f x)
    (hsound : ∀ x, h x = true → f x = true) :
    ∀ x, (F x false || h x) = f x := by
  intro x
  cases hh : h x with
  | false => simpa [hh] using hcorrect x
  | true => simp [hh, hsound x hh]

theorem residual_sound {X : Type} (F : X → Bool → Bool) (h f : X → Bool)
    (hcorrect : ∀ x, F x (h x) = f x)
    (hsound : ∀ x, h x = true → f x = true) :
    ∀ x, F x false = true → f x = true := by
  intro x hx
  rw [← extract F h f hcorrect hsound x, hx]
  rfl

theorem residual_agrees_off_signal {X : Type} (F : X → Bool → Bool) (h f : X → Bool)
    (hcorrect : ∀ x, F x (h x) = f x) :
    ∀ x, h x = false → F x false = f x := by
  intro x hx
  simpa only [hx] using hcorrect x

-- A positive continuation permits a signal to grow, provided it stays below the target.
theorem widen_sound {X : Type} (F : X → Bool → Bool) (q h f : X → Bool)
    (hpositive : ∀ x, F x false = true → F x true = true)
    (hcorrect : ∀ x, F x (q x) = f x)
    (hqh : ∀ x, q x = true → h x = true)
    (hsound : ∀ x, h x = true → f x = true) :
    ∀ x, F x (h x) = f x := by
  intro x
  cases hq : q x with
  | false =>
    cases hh : h x with
    | false => simpa [hq, hh] using hcorrect x
    | true =>
      have hf : f x = true := hsound x hh
      have hF : F x false = true := by simpa [hq, hf] using hcorrect x
      simpa [hh, hf] using hpositive x hF
  | true =>
    have hh := hqh x hq
    simpa [hq, hh] using hcorrect x

-- If one factor is sound, a positive continuation does not need the other factor.
theorem bypass_sound_and {X : Type} (F : X → Bool → Bool) (h k f : X → Bool)
    (hpositive : ∀ x, F x false = true → F x true = true)
    (hcorrect : ∀ x, F x (h x && k x) = f x)
    (hsound : ∀ x, h x = true → f x = true) :
    ∀ x, F x (h x) = f x := by
  apply widen_sound F (fun x => h x && k x) h f hpositive hcorrect
  · intro x hx
    cases hh : h x <;> simp_all
  · exact hsound

-- Soundness alone is not enough when the continuation can negate the signal.
theorem widening_requires_a_positive_continuation :
    ∃ (F : Bool → Bool) (q h f : Bool),
      F q = f ∧ (q = true → h = true) ∧ (h = true → f = true) ∧ F h ≠ f := by
  exact ⟨Bool.not, false, true, true, by decide⟩

abbrev Input := Fin 5 → Bool

def edge (x : Input) := x 0 && x 1
def remainingEdge (x : Input) := x 2 && x 3
def target (x : Input) := edge x || remainingEdge x
def body (x : Input) (b : Bool) := b || (x 0 && x 1 && x 4) || remainingEdge x

theorem example_correct : ∀ x : Input, body x (edge x) = target x := by
  decide +kernel

theorem example_sound : ∀ x : Input, edge x = true → target x = true := by
  intro x hx
  simp [target, hx]

theorem example_positive : ∀ x y : Input, (∀ i, x i = true → y i = true) →
    ∀ b c : Bool, (b = true → c = true) → body x b = true → body y c = true := by
  decide +kernel

def witness : Input := ![true, true, false, false, true]

-- Even a positive residual can contain extra larger accepted sets above the removed edge.
theorem residual_is_not_edge_deletion :
    body witness false = true ∧ remainingEdge witness = false := by
  decide +kernel

theorem example_extracted : ∀ x, (body x false || edge x) = target x :=
  extract body edge target example_correct example_sound

end PEqualNP.Outside.SoundExtraction
