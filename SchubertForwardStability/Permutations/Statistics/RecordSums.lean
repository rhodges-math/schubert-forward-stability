import SchubertForwardStability.Permutations.Statistics.Records

/-! # Finite sums of record indicators

## Main results

Record counts are sums of the complementary indicators. Non-record tails may be
truncated at any support bound, including the empty interval.

## Implementation notes

Every sum is over positive positions. Positions beyond the support are records.
-/

namespace FinitaryPerm

open scoped Classical BigOperators

/-- The record count is the finite sum of complementary natural indicators. -/
theorem recordCount_eq_sum (n : ℕ) (w : FinitaryPerm ℕ+) :
    recordCount n w = ∑ j ∈ positions n, (1 - w.nonRecordIndicator j : ℕ) := by
  rw [recordCount, recordSet, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hr : IsRecord w j <;> simp only [nonRecordIndicator, hr, ite_true, ite_false,
    Nat.sub_zero, Nat.sub_self]

/-- A non-record tail sum can be truncated at any bound supporting the permutation. -/
theorem nonRecordsFrom_eq_sum_supported {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) :
    w.nonRecordsFrom i = ∑ j ∈ (positions n).filter (fun j => i ≤ j),
      w.nonRecordIndicator j := by
  have he : ((w.tailPositions i).filter fun j => ¬IsRecord w j) =
      (((positions n).filter fun j => i ≤ j).filter fun j => ¬IsRecord w j) := by
    ext j
    simp only [Finset.mem_filter, mem_tailPositions, mem_positions]
    constructor
    · rintro ⟨⟨_, hij⟩, hr⟩
      refine ⟨⟨?_, hij⟩, hr⟩
      exact le_of_not_gt fun hj => hr (hw.isRecord_above hj)
    · rintro ⟨⟨_, hij⟩, hr⟩
      refine ⟨⟨?_, hij⟩, hr⟩
      exact le_of_not_gt fun hj => hr (w.isRecord_above hj)
  rw [nonRecordsFrom_eq_card, he, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hr : IsRecord w j <;> simp only [nonRecordIndicator, hr, not_true_eq_false,
    not_false_eq_true, ite_true, ite_false]

/-- A supported permutation has zero non-record tail beyond its support bound. -/
theorem IsSupported.nonRecordsFrom_eq_zero {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (i : ℕ+) (hi : n < (i : ℕ)) : w.nonRecordsFrom i = 0 := by
  rw [nonRecordsFrom_eq_sum_supported hw]
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
  have hb := (mem_positions n j).mp hj
  change (i : ℕ) ≤ (j : ℕ) at hij
  omega

end FinitaryPerm
