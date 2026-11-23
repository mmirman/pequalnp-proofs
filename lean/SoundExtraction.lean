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
