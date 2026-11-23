import Mathlib

namespace PEqualNP.Outside.PivotBarrier

-- These are the two incidence moments of a set of r lines in a plane of order q.
-- d p counts the selected lines through p. The zero set is the uncovered points.
theorem empty_rectangle_bound {α : Type*} [DecidableEq α]
    (P : Finset α) (d : α → ℕ) (q r : ℕ)
    (hn : P.card = q * q + q + 1)
    (hs : ∑ p ∈ P, d p = r * (q + 1))
    (hsq : ∑ p ∈ P, (d p)^2 = r * (q + r)) :
    r * (P.filter (fun p => d p = 0)).card ≤ q * P.card := by
  classical
  let T := P.filter (fun p => d p ≠ 0)
  let U := P.filter (fun p => d p = 0)
  have hpart : U.card + T.card = P.card :=
    Finset.card_filter_add_card_filter_not (s := P) (fun p => d p = 0)
  have sumT : ∑ p ∈ T, d p = r * (q + 1) := by
    rw [← hs]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have : d p = 0 := by simpa [T, hp] using hnot
    exact this
  have sqT : ∑ p ∈ T, (d p)^2 = r * (q + r) := by
    rw [← hsq]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have : d p = 0 := by simpa [T, hp] using hnot
    simp [this]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℕ)) d
  simp only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one, sumT, sqT] at cs
  by_cases hr : r = 0
  · simp [hr]
  · have hrp : 0 < r := Nat.pos_of_ne_zero hr
    have hc : r * (q + 1)^2 ≤ T.card * (q + r) := by
      apply Nat.le_of_mul_le_mul_left (a := r)
      nlinarith [cs]
    change r * U.card ≤ q * P.card
    nlinarith [Nat.zero_le (U.card * q), Nat.zero_le (q * r)]

-- A family of restrictions cannot cover all nonincident point-line pairs
-- a constant fraction of the time using only the incidence-moment estimate.
theorem averaging_requires_q (q N m t : ℕ) (hq : 0 < q) (hN : 0 < N)
    (covered : Fin m → ℕ)
    (hcap : ∀ i, covered i ≤ q * N)
    (hcover : t * (N * q * q) ≤ ∑ i, covered i) :
    t * q ≤ m := by
  have hsum : ∑ i, covered i ≤ m * (q * N) := by
    calc
      ∑ i, covered i ≤ ∑ _ : Fin m, q * N := Finset.sum_le_sum (fun i _ => hcap i)
      _ = m * (q * N) := by simp
  have h : (N * q) * (t * q) ≤ (N * q) * m := by
    nlinarith [hcover, hsum]
  exact (Nat.mul_le_mul_left (Nat.mul_pos hN hq)).mp h

end PEqualNP.Outside.PivotBarrier
