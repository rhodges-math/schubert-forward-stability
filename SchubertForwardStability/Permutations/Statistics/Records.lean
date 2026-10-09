import SchubertForwardStability.Permutations.Finitary.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Records of finitary permutations

## Main definitions

* `IsRecord`: a value strictly exceeding all preceding values.
* `leftInversions`, `leftInversionCount`: preceding positions with larger values.
* `recordSet`, `recordCount`: records in an initial positive interval.
* `nonRecordIndicator`, `nonRecordsFrom`: non-record indicators and their finite tail sum.

## Implementation notes

Positions and values are positive integers. Every position beyond the support bound is
a record, so the tail sum may be truncated at the positive forward-stability bound.
-/

namespace FinitaryPerm

open scoped Classical BigOperators

/-- A position is a record when its value exceeds every preceding value. -/
def IsRecord (w : FinitaryPerm ℕ+) (j : ℕ+) : Prop :=
  ∀ k : ℕ+, k < j → w k < w j

/-- Every position of the identity permutation is a record. -/
theorem isRecord_one (j : ℕ+) : IsRecord 1 j := fun _ h => h

/-- The first positive position is always a record. -/
theorem isRecord_first (w : FinitaryPerm ℕ+) : IsRecord w 1 := by
  intro k hk
  exact False.elim ((not_lt_of_ge (one_le : 1 ≤ k)) hk)

/-- A position above a support bound is a record. -/
theorem IsSupported.isRecord_above {n : ℕ} {w : FinitaryPerm ℕ+}
    (h : IsSupported n w) {j : ℕ+} (hj : n < (j : ℕ)) : IsRecord w j := by
  intro k hk
  rw [h j hj]
  by_cases hkn : (k : ℕ) ≤ n
  · have hwk := (h.apply_le_iff k).mpr hkn
    change (w k : ℕ) < (j : ℕ)
    exact lt_of_le_of_lt hwk hj
  · rw [h k (lt_of_not_ge hkn)]
    exact hk

/-- All positions beyond forward stability are records. -/
theorem isRecord_above (w : FinitaryPerm ℕ+) {j : ℕ+}
    (hj : w.forwardStability < (j : ℕ)) : IsRecord w j :=
  w.isSupported_forwardStability.isRecord_above hj

/-- Initial-interval membership at a predecessor is strict comparison with the position. -/
theorem mem_positions_pred (j k : ℕ+) : k ∈ positions ((j : ℕ) - 1) ↔ k < j := by
  rw [mem_positions]
  change (k : ℕ) ≤ (j : ℕ) - 1 ↔ (k : ℕ) < (j : ℕ)
  constructor
  · intro h
    exact lt_of_le_of_lt h (Nat.sub_lt (PNat.pos j) (by decide : 0 < 1))
  · exact Nat.le_sub_one_of_lt

/-- The preceding positions carrying values greater than the value at `j`. -/
noncomputable def leftInversions (w : FinitaryPerm ℕ+) (j : ℕ+) : Finset ℕ+ :=
  (positions ((j : ℕ) - 1)).filter fun k => w j < w k

/-- Membership in left inversions is exactly the two strict inequalities. -/
@[simp]
theorem mem_leftInversions (w : FinitaryPerm ℕ+) (j k : ℕ+) :
    k ∈ w.leftInversions j ↔ k < j ∧ w j < w k := by
  simp only [leftInversions, Finset.mem_filter, mem_positions_pred]

/-- The number of preceding positions whose values exceed the value at `j`. -/
noncomputable def leftInversionCount (w : FinitaryPerm ℕ+) (j : ℕ+) : ℕ :=
  (w.leftInversions j).card

/-- A record has no left inversions, and conversely. -/
theorem isRecord_iff_leftInversions_empty (w : FinitaryPerm ℕ+) (j : ℕ+) :
    IsRecord w j ↔ w.leftInversions j = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h k hk
    exact (not_lt_of_gt (h k (mem_leftInversions w j k |>.mp hk).1))
      (mem_leftInversions w j k |>.mp hk).2
  · intro h k hk
    apply lt_of_le_of_ne
    · exact le_of_not_gt fun hgt => h k ((mem_leftInversions w j k).mpr ⟨hk, hgt⟩)
    · exact fun he => (ne_of_lt hk) (w.injective he)

/-- A position is a record exactly when its left-inversion count is zero. -/
theorem isRecord_iff_leftInversionCount (w : FinitaryPerm ℕ+) (j : ℕ+) :
    IsRecord w j ↔ w.leftInversionCount j = 0 := by
  rw [leftInversionCount, Finset.card_eq_zero, isRecord_iff_leftInversions_empty]

/-- The left-inversion count is bounded by the number of preceding positions. -/
theorem leftInversionCount_le (w : FinitaryPerm ℕ+) (j : ℕ+) :
    w.leftInversionCount j ≤ (j : ℕ) - 1 := by
  exact (Finset.card_filter_le _ _).trans_eq (card_positions _)

/-- The records among the first `n` positive positions. -/
noncomputable def recordSet (n : ℕ) (w : FinitaryPerm ℕ+) : Finset ℕ+ :=
  (positions n).filter (IsRecord w)

/-- Record-set membership combines interval membership and the record property. -/
@[simp]
theorem mem_recordSet (n : ℕ) (w : FinitaryPerm ℕ+) (j : ℕ+) :
    j ∈ recordSet n w ↔ (j : ℕ) ≤ n ∧ IsRecord w j := by
  simp only [recordSet, Finset.mem_filter, mem_positions]

/-- The number of records among the first `n` positive positions. -/
noncomputable def recordCount (n : ℕ) (w : FinitaryPerm ℕ+) : ℕ := (recordSet n w).card

/-- There are no record positions in the empty initial interval. -/
@[simp]
theorem recordSet_zero (w : FinitaryPerm ℕ+) : recordSet 0 w = ∅ := by
  rw [recordSet, positions_zero, Finset.filter_empty]

/-- The size-zero record count vanishes. -/
@[simp]
theorem recordCount_zero (w : FinitaryPerm ℕ+) : recordCount 0 w = 0 := by
  rw [recordCount, recordSet_zero, Finset.card_empty]

/-- The record count cannot exceed the ambient size. -/
theorem recordCount_le (n : ℕ) (w : FinitaryPerm ℕ+) : recordCount n w ≤ n :=
  (Finset.card_filter_le _ _).trans_eq (card_positions n)

/-- Every initial position is a record of the identity. -/
@[simp]
theorem recordSet_one (n : ℕ) : recordSet n 1 = positions n := by
  ext j
  simp only [mem_recordSet, mem_positions, isRecord_one, and_true]

/-- The identity has exactly `n` records in size `n`. -/
@[simp]
theorem recordCount_one (n : ℕ) : recordCount n 1 = n := by
  rw [recordCount, recordSet_one, card_positions]

/-- The non-record indicator is zero at records and one at other positions. -/
noncomputable def nonRecordIndicator (w : FinitaryPerm ℕ+) (j : ℕ+) : ℕ :=
  if IsRecord w j then 0 else 1

/-- A record has zero non-record indicator. -/
theorem nonRecordIndicator_eq_zero {w : FinitaryPerm ℕ+} {j : ℕ+}
    (h : IsRecord w j) : w.nonRecordIndicator j = 0 := ite_eq_left h

/-- A non-record has non-record indicator one. -/
theorem nonRecordIndicator_eq_one {w : FinitaryPerm ℕ+} {j : ℕ+}
    (h : ¬IsRecord w j) : w.nonRecordIndicator j = 1 := ite_eq_right h

/-- The non-record indicator vanishes beyond forward stability. -/
theorem nonRecordIndicator_above (w : FinitaryPerm ℕ+) {j : ℕ+}
    (hj : w.forwardStability < (j : ℕ)) : w.nonRecordIndicator j = 0 :=
  nonRecordIndicator_eq_zero (w.isRecord_above hj)

/-- The positive positions from `i` through the forward-stability bound. -/
noncomputable def tailPositions (w : FinitaryPerm ℕ+) (i : ℕ+) : Finset ℕ+ :=
  (positions w.forwardStability).filter fun j => i ≤ j

/-- Tail-position membership is the pair of endpoint inequalities. -/
@[simp]
theorem mem_tailPositions (w : FinitaryPerm ℕ+) (i j : ℕ+) :
    j ∈ w.tailPositions i ↔ (j : ℕ) ≤ w.forwardStability ∧ i ≤ j := by
  simp only [tailPositions, Finset.mem_filter, mem_positions]

/-- A tail starting above the forward-stability bound is empty. -/
theorem tailPositions_above (w : FinitaryPerm ℕ+) {i : ℕ+}
    (hi : w.forwardStability < (i : ℕ)) : w.tailPositions i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, hij⟩ := (mem_tailPositions w i j).mp hj
  exact (not_le_of_gt hi) (le_trans hij hj)

/-- Splitting a nonempty tail separates its first positive position. -/
theorem tailPositions_split (w : FinitaryPerm ℕ+) {i : ℕ+}
    (hi : (i : ℕ) ≤ w.forwardStability) :
    w.tailPositions i = insert i (w.tailPositions (i + 1)) := by
  ext j
  simp only [mem_tailPositions, Finset.mem_insert]
  have hsucc : ((i + 1 : ℕ+) : ℕ) = (i : ℕ) + 1 := rfl
  constructor
  · rintro ⟨hj, hij⟩
    by_cases he : j = i
    · exact Or.inl he
    · right
      refine ⟨hj, ?_⟩
      change ((i + 1 : ℕ+) : ℕ) ≤ (j : ℕ)
      rw [hsucc]
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h => he (PNat.eq h).symm
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hij hne)
  · rintro (rfl | ⟨hj, hij⟩)
    · exact ⟨hi, le_rfl⟩
    · refine ⟨hj, ?_⟩
      change (i : ℕ) ≤ (j : ℕ)
      change ((i + 1 : ℕ+) : ℕ) ≤ (j : ℕ) at hij
      rw [hsucc] at hij
      exact le_trans (Nat.le_succ _) hij

/-- The finite sum of non-record indicators at all positions at least `i`. -/
noncomputable def nonRecordsFrom (w : FinitaryPerm ℕ+) (i : ℕ+) : ℕ :=
  ∑ j ∈ w.tailPositions i, w.nonRecordIndicator j

/-- The non-record tail sum vanishes beyond forward stability. -/
theorem nonRecordsFrom_above (w : FinitaryPerm ℕ+) {i : ℕ+}
    (hi : w.forwardStability < (i : ℕ)) : w.nonRecordsFrom i = 0 := by
  rw [nonRecordsFrom, tailPositions_above w hi, Finset.sum_empty]

/-- The tail sum counts the non-record positions in that tail. -/
theorem nonRecordsFrom_eq_card (w : FinitaryPerm ℕ+) (i : ℕ+) :
    w.nonRecordsFrom i = ((w.tailPositions i).filter fun j => ¬IsRecord w j).card := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : IsRecord w j
  · rw [nonRecordIndicator_eq_zero h, ite_eq_right (not_not_intro h)]
  · rw [nonRecordIndicator_eq_one h, ite_eq_left h]

/-- Advancing the tail removes exactly the current non-record indicator. -/
theorem nonRecordsFrom_succ (w : FinitaryPerm ℕ+) (i : ℕ+) :
    w.nonRecordsFrom i = w.nonRecordIndicator i + w.nonRecordsFrom (i + 1) := by
  by_cases hi : (i : ℕ) ≤ w.forwardStability
  · have hnot : i ∉ w.tailPositions (i + 1) := by
      rw [mem_tailPositions]
      intro h
      have hs : ((i + 1 : ℕ+) : ℕ) ≤ (i : ℕ) := h.2
      change (i : ℕ) + 1 ≤ (i : ℕ) at hs
      exact Nat.not_succ_le_self _ hs
    rw [nonRecordsFrom, tailPositions_split w hi, Finset.sum_insert hnot, nonRecordsFrom]
  · have hgt := lt_of_not_ge hi
    have hnext : w.forwardStability < ((i + 1 : ℕ+) : ℕ) :=
      lt_trans hgt (Nat.lt_succ_self _)
    rw [nonRecordsFrom_above w hgt, nonRecordIndicator_above w hgt,
      nonRecordsFrom_above w hnext, zero_add]

/-- Every non-record tail sum of identity vanishes. -/
@[simp]
theorem nonRecordsFrom_one (i : ℕ+) : nonRecordsFrom 1 i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact nonRecordIndicator_eq_zero (isRecord_one j)

/-- Records and non-records partition any initial interval containing the support. -/
theorem recordCount_add_nonRecords {n : ℕ} (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    recordCount n w + w.nonRecordsFrom 1 = n := by
  have hset : ((w.tailPositions 1).filter fun j => ¬IsRecord w j) =
      ((positions n).filter fun j => ¬IsRecord w j) := by
    ext j
    simp only [Finset.mem_filter, mem_tailPositions, mem_positions]
    constructor
    · rintro ⟨_, hnr⟩
      refine ⟨?_, hnr⟩
      by_contra hn
      exact hnr (hw.isRecord_above (lt_of_not_ge hn))
    · rintro ⟨_, hnr⟩
      refine ⟨⟨?_, one_le⟩, hnr⟩
      by_contra hn
      exact hnr (w.isRecord_above (lt_of_not_ge hn))
  rw [nonRecordsFrom_eq_card, hset, recordCount, recordSet,
    Finset.card_filter_add_card_filter_not, card_positions]

end FinitaryPerm
