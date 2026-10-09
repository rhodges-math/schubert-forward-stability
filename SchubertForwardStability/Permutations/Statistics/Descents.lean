import SchubertForwardStability.Permutations.Statistics.Inversions

/-! # Adjacent descents

## Main definitions

* `HasDescent`: an adjacent decrease in the one-line values.
* `descentSet`: the finite set of positions with adjacent decreases.

## Implementation notes

Descent positions are positive integers and lie strictly below every support bound.
-/

namespace FinitaryPerm

open scoped Classical

/-- A descent is an adjacent decrease of permutation values. -/
def HasDescent (w : FinitaryPerm ℕ+) (i : ℕ+) : Prop := w (i + 1) < w i

/-- A descent position lies strictly below any support bound. -/
theorem IsSupported.descent_lt {n : ℕ} {w : FinitaryPerm ℕ+} (hw : IsSupported n w)
    {i : ℕ+} (hi : HasDescent w i) : (i : ℕ) < n := by
  by_contra hn
  have hnext : n < ((i + 1 : ℕ+) : ℕ) :=
    lt_of_le_of_lt (le_of_not_gt hn) (Nat.lt_succ_self _)
  have hinc : i < i + 1 := Nat.lt_succ_self (i : ℕ)
  exact (not_lt_of_gt (hw.isRecord_above hnext i hinc)) hi

/-- The finite set of positions at which adjacent values decrease. -/
noncomputable def descentSet (w : FinitaryPerm ℕ+) : Finset ℕ+ :=
  (positions w.forwardStability).filter (HasDescent w)

/-- Membership in the descent set is the adjacent decrease itself. -/
@[simp]
theorem mem_descentSet (w : FinitaryPerm ℕ+) (i : ℕ+) :
    i ∈ w.descentSet ↔ HasDescent w i := by
  simp only [descentSet, Finset.mem_filter, mem_positions]
  exact and_iff_right_of_imp fun h => le_of_lt (w.isSupported_forwardStability.descent_lt h)

/-- The identity has no descents. -/
@[simp]
theorem descentSet_one : descentSet (1 : FinitaryPerm ℕ+) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have h := (mem_descentSet 1 i).mp hi
  exact (not_lt_of_ge (Nat.le_succ (i : ℕ))) h

end FinitaryPerm
