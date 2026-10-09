import SchubertForwardStability.Permutations.Statistics.SuffixMaximum
import Mathlib.Algebra.Order.Ring.Abs

/-! # Record walks

## Main definitions

* `recordWalk`: the sum of two non-record tails plus the position minus one.
* `recordWalkStep`: the difference between consecutive walk values.
* `recordWalkMaxAt`: the maximum through a specified ambient size plus one.
* `recordWalkMax`: the maximum through the greater forward bound plus one.

## Main results

The increments are one minus the two non-record indicators and lie between minus
one and one. Each finite maximum is attained and contains every indexed walk value.

## Implementation notes

Positions are positive integers and walk values are integers. All values are
nonnegative, allowing finite maxima to use natural-number suprema followed by a cast.
-/

namespace RecordStability

open FinitaryPerm

open scoped Classical

/-- The integer walk obtained from two non-record tails. -/
noncomputable def recordWalk (u v : FinitaryPerm ℕ+) (i : ℕ+) : ℤ :=
  (u.nonRecordsFrom i : ℤ) + (v.nonRecordsFrom i : ℤ) + (i : ℕ) - 1

/-- The increment from a positive position to its successor. -/
noncomputable def recordWalkStep (u v : FinitaryPerm ℕ+) (i : ℕ+) : ℤ :=
  recordWalk u v (i + 1) - recordWalk u v i

/-- The maximum walk value through the position one greater than an ambient size. -/
noncomputable def recordWalkMaxAt (n : ℕ) (u v : FinitaryPerm ℕ+) : ℤ :=
  ((positions (n + 1)).sup fun i =>
    u.nonRecordsFrom i + v.nonRecordsFrom i + (i : ℕ) - 1 : ℕ)

/-- The finite maximum through one greater than the larger individual support bound. -/
noncomputable def recordWalkMax (u v : FinitaryPerm ℕ+) : ℤ :=
  (pairRecordBound u v : ℤ)

/-- A walk value is the cast of its natural-number expression. -/
theorem recordWalk_eq_nat (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    recordWalk u v i =
      ((u.nonRecordsFrom i + v.nonRecordsFrom i + (i : ℕ) - 1 : ℕ) : ℤ) := by
  unfold recordWalk
  have hi := PNat.pos i
  omega

/-- Every record-walk value is nonnegative. -/
theorem recordWalk_nonneg (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    0 ≤ recordWalk u v i := by
  rw [recordWalk_eq_nat]
  exact Int.natCast_nonneg _

/-- Interchanging the two permutations does not change the walk. -/
theorem recordWalk_comm (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    recordWalk u v i = recordWalk v u i := by
  simp only [recordWalk, add_comm (u.nonRecordsFrom i : ℤ) (v.nonRecordsFrom i : ℤ)]

/-- A walk increment is one minus its two non-record indicators. -/
theorem recordWalkStep_eq (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    recordWalkStep u v i =
      1 - (u.nonRecordIndicator i : ℤ) - (v.nonRecordIndicator i : ℤ) := by
  have hu := nonRecordsFrom_succ u i
  have hv := nonRecordsFrom_succ v i
  have hi : (((i + 1 : ℕ+) : ℕ) : ℤ) = ((i : ℕ) : ℤ) + 1 := by
    change (((i : ℕ) + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + 1
    rw [Nat.cast_add, Nat.cast_one]
  unfold recordWalkStep recordWalk
  rw [hu, hv, hi]
  simp only [Nat.cast_add]
  omega

/-- Walk increments lie between minus one and one. -/
theorem recordWalkStep_bounds (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    -1 ≤ recordWalkStep u v i ∧ recordWalkStep u v i ≤ 1 := by
  have hu : u.nonRecordIndicator i ≤ 1 := by
    unfold nonRecordIndicator
    split <;> omega
  have hv : v.nonRecordIndicator i ≤ 1 := by
    unfold nonRecordIndicator
    split <;> omega
  rw [recordWalkStep_eq]
  omega

/-- A walk increment has one of the three values minus one, zero or one. -/
theorem recordWalkStep_values (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    recordWalkStep u v i = -1 ∨ recordWalkStep u v i = 0 ∨
      recordWalkStep u v i = 1 := by
  have h := recordWalkStep_bounds u v i
  omega

/-- The absolute value of every walk increment is at most one. -/
theorem abs_recordWalkStep_le (u v : FinitaryPerm ℕ+) (i : ℕ+) :
    |recordWalkStep u v i| ≤ 1 := by
  exact abs_le.mpr (recordWalkStep_bounds u v i)

/-- Every indexed walk value is bounded by the finite ambient maximum. -/
theorem recordWalk_le_maxAt {n : ℕ} (u v : FinitaryPerm ℕ+) {i : ℕ+}
    (hi : (i : ℕ) ≤ n + 1) : recordWalk u v i ≤ recordWalkMaxAt n u v := by
  have h := Finset.le_sup (f := fun k : ℕ+ =>
    u.nonRecordsFrom k + v.nonRecordsFrom k + (k : ℕ) - 1)
    ((mem_positions (n + 1) i).mpr hi)
  rw [recordWalk_eq_nat]
  unfold recordWalkMaxAt
  omega

/-- Increasing the ambient bound cannot decrease the finite maximum. -/
theorem recordWalkMaxAt_mono {m n : ℕ} (h : m ≤ n) (u v : FinitaryPerm ℕ+) :
    recordWalkMaxAt m u v ≤ recordWalkMaxAt n u v := by
  have hs : (positions (m + 1)).sup (fun k : ℕ+ =>
      u.nonRecordsFrom k + v.nonRecordsFrom k + (k : ℕ) - 1) ≤
      (positions (n + 1)).sup (fun k : ℕ+ =>
        u.nonRecordsFrom k + v.nonRecordsFrom k + (k : ℕ) - 1) := by
    apply Finset.sup_le
    intro i hi
    exact Finset.le_sup (f := fun k : ℕ+ =>
      u.nonRecordsFrom k + v.nonRecordsFrom k + (k : ℕ) - 1)
      ((mem_positions (n + 1) i).mpr
      (by have him := (mem_positions (m + 1) i).mp hi; omega))
  unfold recordWalkMaxAt
  omega

/-- The finite ambient maximum is attained at one of its positive positions. -/
theorem exists_recordWalk_eq_maxAt (n : ℕ) (u v : FinitaryPerm ℕ+) :
    ∃ i : ℕ+, (i : ℕ) ≤ n + 1 ∧ recordWalk u v i = recordWalkMaxAt n u v := by
  have hn : (positions (n + 1)).Nonempty :=
    ⟨1, (mem_positions (n + 1) 1).mpr (Nat.succ_pos n)⟩
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup (positions (n + 1)) hn
    (fun k : ℕ+ => u.nonRecordsFrom k + v.nonRecordsFrom k + (k : ℕ) - 1)
  refine ⟨i, (mem_positions (n + 1) i).mp hi, ?_⟩
  rw [recordWalk_eq_nat]
  unfold recordWalkMaxAt
  exact congrArg (fun k : ℕ => (k : ℤ)) he.symm

/-- The support-bounded maximum is the corresponding ambient maximum. -/
theorem recordWalkMax_eq_maxAt (u v : FinitaryPerm ℕ+) :
    recordWalkMax u v = recordWalkMaxAt (max u.forwardStability v.forwardStability) u v :=
  rfl

/-- Every walk value in the support-bounded interval lies below the maximum. -/
theorem recordWalk_le_max (u v : FinitaryPerm ℕ+) {i : ℕ+}
    (hi : (i : ℕ) ≤ max u.forwardStability v.forwardStability + 1) :
    recordWalk u v i ≤ recordWalkMax u v := by
  rw [recordWalkMax_eq_maxAt]
  exact recordWalk_le_maxAt u v hi

/-- The support-bounded record-walk maximum is at least one. -/
theorem one_le_recordWalkMax (u v : FinitaryPerm ℕ+) : 1 ≤ recordWalkMax u v := by
  have h := one_le_pairRecordBound u v
  unfold recordWalkMax
  omega

/-- A larger ambient interval bounds the support-bounded walk maximum. -/
theorem recordWalkMax_le_maxAt {n : ℕ} (u v : FinitaryPerm ℕ+)
    (hu : u.forwardStability ≤ n) (hv : v.forwardStability ≤ n) :
    recordWalkMax u v ≤ recordWalkMaxAt n u v := by
  rw [recordWalkMax_eq_maxAt]
  exact recordWalkMaxAt_mono (max_le hu hv) u v

/-- For two identity permutations the walk is position minus one. -/
theorem recordWalk_one_one (i : ℕ+) : recordWalk 1 1 i = (i : ℕ) - 1 := by
  simp only [recordWalk, nonRecordsFrom_one, Nat.cast_zero, zero_add]

end RecordStability
