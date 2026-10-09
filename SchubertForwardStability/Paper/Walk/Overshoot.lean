import SchubertForwardStability.Paper.Walk.Tails
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Upward-step bounds for finite record-walk overshoots

The record walk goes up exactly at positions that are records of both permutations, and
every step is at most its upward indicator. Hence the increase of the walk over a segment,
and the excess of a tail maximum over its first value, are at most the number of upward
steps.
-/

namespace RecordStability

open FinitaryPerm
open scoped Classical BigOperators

/-- The integer indicator of an upward walk step. -/
noncomputable def upwardIndicator (u v : FinitaryPerm ℕ+) (i : ℕ+) : ℤ :=
  if recordWalkStep u v i = 1 then 1 else 0

/-- Upward steps occur precisely when both permutations have a record at that position. -/
theorem upwardIndicator_eq_records (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    upwardIndicator u v i = if IsRecord u i ∧ IsRecord v i then 1 else 0 := by
  by_cases hu : IsRecord u i <;> by_cases hv : IsRecord v i <;>
    simp [upwardIndicator, recordWalkStep_eq, nonRecordIndicator, hu, hv]

/-- An upward indicator is nonnegative. -/
theorem upwardIndicator_nonneg (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    0 ≤ upwardIndicator u v i := by
  unfold upwardIndicator
  split <;> omega

/-- Each step is bounded above by its upward indicator. -/
theorem recordWalkStep_le_upward (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    recordWalkStep u v i ≤ upwardIndicator u v i := by
  have hs := recordWalkStep_values u v i
  unfold upwardIndicator
  split <;> omega

/-- The walk's increase over a finite segment is bounded by its number of upward steps. -/
theorem recordWalk_le_upward_sum (u v : FinitaryPerm ℕ+) (r s : ℕ) :
    recordWalk u v (r + s).succPNat ≤ recordWalk u v r.succPNat +
      ∑ k ∈ Finset.range s, upwardIndicator u v (r + k).succPNat := by
  induction s with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ s ih =>
    have hs := recordWalkStep_le_upward u v (r + s).succPNat
    have hi : (r + (s + 1)).succPNat = (r + s).succPNat + 1 := by
      apply PNat.eq
      change r + (s + 1) + 1 = r + s + 1 + 1
      omega
    have hw : recordWalk u v (r + (s + 1)).succPNat =
        recordWalk u v (r + s).succPNat + recordWalkStep u v (r + s).succPNat := by
      rw [hi]
      unfold recordWalkStep
      omega
    rw [Finset.sum_range_succ, hw]
    omega

/-- A nonempty tail maximum exceeds its first value by at most the full upward-step count. -/
theorem recordWalkMaxFrom_le_upward {n : ℕ} (i : ℕ+) (u v : FinitaryPerm ℕ+)
    (hi : (i : ℕ) ≤ n + 1) :
    recordWalkMaxFrom n i u v - recordWalk u v i ≤
      ∑ k ∈ Finset.range (n + 1 - (i : ℕ)),
        upwardIndicator u v ((i : ℕ) - 1 + k).succPNat := by
  obtain ⟨j, hij, hj, he⟩ := exists_recordWalk_eq_maxFrom i u v hi
  have hp := PNat.pos i
  have hstart : ((i : ℕ) - 1).succPNat = i := by
    apply PNat.eq
    change (i : ℕ) - 1 + 1 = (i : ℕ)
    omega
  have hend : ((i : ℕ) - 1 + ((j : ℕ) - (i : ℕ))).succPNat = j := by
    apply PNat.eq
    change (i : ℕ) - 1 + ((j : ℕ) - (i : ℕ)) + 1 = (j : ℕ)
    change (i : ℕ) ≤ (j : ℕ) at hij
    omega
  have hw := recordWalk_le_upward_sum u v ((i : ℕ) - 1) ((j : ℕ) - (i : ℕ))
  rw [hstart, hend, he] at hw
  have hsum :
      (∑ k ∈ Finset.range ((j : ℕ) - (i : ℕ)),
        upwardIndicator u v ((i : ℕ) - 1 + k).succPNat) ≤
      ∑ k ∈ Finset.range (n + 1 - (i : ℕ)),
        upwardIndicator u v ((i : ℕ) - 1 + k).succPNat := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (Nat.sub_le_sub_right hj (i : ℕ))
    · intro k _ _
      exact upwardIndicator_nonneg u v _
  omega

end RecordStability
