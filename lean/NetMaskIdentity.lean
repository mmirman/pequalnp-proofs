import Mathlib

namespace PEqualNP.Outside.NetMaskIdentity

def edge (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) ||
  (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)

def factored (x : Fin 6 → Bool) : Bool :=
  (x 0 || x 1 || (x 2 && x 5)) &&
  ((x 0 || x 2 || x 4) && (x 1 || x 2 || x 3))

lemma net_identity : ∀ x, factored x = edge x := by decide +kernel

lemma distributed_mask : ∀ (p q r s : Bool),
    ((p || s) && ((q || s) && (r || s))) = ((p && (q && r)) || s) := by
  decide

theorem masked_net (x : Fin 6 → Bool) (s : Bool) :
    (((x 0 || x 1 || (x 2 && x 5)) || s) &&
      (((x 0 || x 2 || x 4) || s) && ((x 1 || x 2 || x 3) || s))) =
      (edge x || s) := by
  rw [distributed_mask]
  exact congrArg (fun b => b || s) (net_identity x)

theorem predicted_deficit (r : ℕ) (hr : 2 ≤ r) :
    3*r + (6*r+3) + 2*(r-2) + 1 + 2 + (r-2) = 12*r := by omega

theorem predicted_failure (r : ℕ) (hr : 3 ≤ r) :
    ¬ (12*r ≤ 3*r + (6*r+3) + 2*(r-2) + 1 + 2) := by omega

end PEqualNP.Outside.NetMaskIdentity
