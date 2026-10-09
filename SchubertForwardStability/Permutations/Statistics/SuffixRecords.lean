import SchubertForwardStability.Permutations.Statistics.Records

/-! # Non-records in a suffix

## Main definitions

* `IsSuffixNonRecord`: an earlier larger value within the suffix starting at a position.
* `suffixNonRecords`, `suffixNonRecordCount`: the finite set and count of these positions.

## Main results

The suffix count is bounded by the global non-record tail count. Equality holds when
the starting position is a global record. The finite count is independent of the chosen
support bound.

## Implementation notes

Positions and values are positive integers. The starting position itself is not counted.
Every counted position lies at most at the positive forward-stability bound.
-/

namespace FinitaryPerm

open scoped Classical

/-- A suffix non-record has an earlier larger value at or after its starting position. -/
def IsSuffixNonRecord (w : FinitaryPerm ℕ+) (i j : ℕ+) : Prop :=
  ∃ k : ℕ+, i ≤ k ∧ k < j ∧ w j < w k

/-- A suffix non-record occurs strictly after the starting position. -/
theorem IsSuffixNonRecord.start_lt {w : FinitaryPerm ℕ+} {i j : ℕ+}
    (h : IsSuffixNonRecord w i j) : i < j := by
  obtain ⟨k, hik, hkj, _⟩ := h
  exact lt_of_le_of_lt hik hkj

/-- Every suffix non-record is a global non-record. -/
theorem IsSuffixNonRecord.not_record {w : FinitaryPerm ℕ+} {i j : ℕ+}
    (h : IsSuffixNonRecord w i j) : ¬IsRecord w j := by
  obtain ⟨k, _, hkj, hvalue⟩ := h
  intro hrecord
  exact (not_lt_of_gt (hrecord k hkj)) hvalue

/-- A suffix non-record lies within any support bound. -/
theorem IsSuffixNonRecord.le_bound {w : FinitaryPerm ℕ+} {i j : ℕ+} {n : ℕ}
    (h : IsSuffixNonRecord w i j) (hw : IsSupported n w) : (j : ℕ) ≤ n := by
  by_contra hj
  exact h.not_record (hw.isRecord_above (lt_of_not_ge hj))

/-- A suffix non-record lies at most at the forward-stability bound. -/
theorem IsSuffixNonRecord.le_forward {w : FinitaryPerm ℕ+} {i j : ℕ+}
    (h : IsSuffixNonRecord w i j) : (j : ℕ) ≤ w.forwardStability :=
  h.le_bound w.isSupported_forwardStability

/-- At a global record, suffix non-records are exactly the later global non-records. -/
theorem suffixNonRecord_iff_of_record {w : FinitaryPerm ℕ+} {i j : ℕ+}
    (hrecord : IsRecord w i) (hij : i < j) :
    IsSuffixNonRecord w i j ↔ ¬IsRecord w j := by
  constructor
  · exact IsSuffixNonRecord.not_record
  · intro hnonrecord
    by_contra hnone
    apply hnonrecord
    intro k hkj
    apply lt_of_not_ge
    intro hvalue
    have hne : w j ≠ w k := fun h => (ne_of_gt hkj) (w.injective h)
    have hgt : w j < w k := lt_of_le_of_ne hvalue hne
    by_cases hik : i ≤ k
    · exact hnone ⟨k, hik, hkj, hgt⟩
    · have hki : k < i := lt_of_not_ge hik
      exact hnone ⟨i, le_rfl, hij, lt_trans hgt (hrecord k hki)⟩

/-- The finite set of suffix non-record positions. -/
noncomputable def suffixNonRecords (w : FinitaryPerm ℕ+) (i : ℕ+) : Finset ℕ+ :=
  (positions w.forwardStability).filter (IsSuffixNonRecord w i)

/-- Membership in the suffix non-record set is the earlier-larger-value condition. -/
@[simp]
theorem mem_suffixNonRecords (w : FinitaryPerm ℕ+) (i j : ℕ+) :
    j ∈ w.suffixNonRecords i ↔ IsSuffixNonRecord w i j := by
  simp only [suffixNonRecords, Finset.mem_filter, mem_positions]
  exact ⟨fun h => h.2, fun h => ⟨h.le_forward, h⟩⟩

/-- The number of non-records in the suffix starting at a positive position. -/
noncomputable def suffixNonRecordCount (w : FinitaryPerm ℕ+) (i : ℕ+) : ℕ :=
  (w.suffixNonRecords i).card

/-- A suffix count can be truncated at any support bound without changing its value. -/
theorem suffixNonRecords_eq_filter {w : FinitaryPerm ℕ+} {n : ℕ}
    (hw : IsSupported n w) (i : ℕ+) :
    w.suffixNonRecords i = (positions n).filter (IsSuffixNonRecord w i) := by
  ext j
  simp only [mem_suffixNonRecords, Finset.mem_filter, mem_positions]
  exact ⟨fun h => ⟨h.le_bound hw, h⟩, fun h => h.2⟩

/-- The suffix count is the cardinality of its witness condition within any support bound. -/
theorem suffixNonRecordCount_eq_card {w : FinitaryPerm ℕ+} {n : ℕ}
    (hw : IsSupported n w) (i : ℕ+) :
    w.suffixNonRecordCount i = ((positions n).filter (IsSuffixNonRecord w i)).card := by
  rw [suffixNonRecordCount, suffixNonRecords_eq_filter hw]

/-- The suffix non-record set is empty at or beyond forward stability. -/
theorem suffixNonRecords_eq_empty (w : FinitaryPerm ℕ+) {i : ℕ+}
    (hi : w.forwardStability ≤ (i : ℕ)) : w.suffixNonRecords i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have h := (mem_suffixNonRecords w i j).mp hj
  have hlt : (i : ℕ) < (j : ℕ) := h.start_lt
  exact (not_lt_of_ge (h.le_forward.trans hi)) hlt

/-- The suffix count vanishes at or beyond forward stability. -/
theorem suffixNonRecordCount_eq_zero (w : FinitaryPerm ℕ+) {i : ℕ+}
    (hi : w.forwardStability ≤ (i : ℕ)) : w.suffixNonRecordCount i = 0 := by
  rw [suffixNonRecordCount, suffixNonRecords_eq_empty w hi, Finset.card_empty]

/-- A positive suffix count starts strictly before forward stability. -/
theorem suffixNonRecordCount_pos_lt {w : FinitaryPerm ℕ+} {i : ℕ+}
    (hi : 0 < w.suffixNonRecordCount i) : (i : ℕ) < w.forwardStability := by
  by_contra h
  rw [suffixNonRecordCount_eq_zero w (le_of_not_gt h)] at hi
  exact (Nat.lt_irrefl 0) hi

/-- Every suffix non-record is a non-record in the global tail beginning one position later. -/
theorem suffixNonRecords_subset (w : FinitaryPerm ℕ+) (i : ℕ+) :
    w.suffixNonRecords i ⊆ (w.tailPositions (i + 1)).filter fun j => ¬IsRecord w j := by
  intro j hj
  have h := (mem_suffixNonRecords w i j).mp hj
  apply Finset.mem_filter.mpr
  refine ⟨(mem_tailPositions w (i + 1) j).mpr ⟨h.le_forward, ?_⟩, h.not_record⟩
  change (i : ℕ) + 1 ≤ (j : ℕ)
  exact Nat.succ_le_of_lt h.start_lt

/-- The suffix count is bounded by the global non-record tail count. -/
theorem suffixNonRecordCount_le (w : FinitaryPerm ℕ+) (i : ℕ+) :
    w.suffixNonRecordCount i ≤ w.nonRecordsFrom (i + 1) := by
  rw [suffixNonRecordCount, nonRecordsFrom_eq_card]
  exact Finset.card_le_card (suffixNonRecords_subset w i)

/-- A suffix starting at a global record contains every later global non-record. -/
theorem suffixNonRecords_eq_of_record {w : FinitaryPerm ℕ+} {i : ℕ+}
    (hi : IsRecord w i) :
    w.suffixNonRecords i = (w.tailPositions (i + 1)).filter fun j => ¬IsRecord w j := by
  apply Finset.Subset.antisymm (suffixNonRecords_subset w i)
  intro j hj
  obtain ⟨hjt, hnr⟩ := Finset.mem_filter.mp hj
  have hij : i < j := by
    have hsucc := (mem_tailPositions w (i + 1) j).mp hjt |>.2
    change (i : ℕ) + 1 ≤ (j : ℕ) at hsucc
    exact Nat.lt_of_succ_le hsucc
  exact (mem_suffixNonRecords w i j).mpr ((suffixNonRecord_iff_of_record hi hij).mpr hnr)

/-- At a global record, the suffix count equals the later global non-record tail count. -/
theorem suffixNonRecordCount_eq_of_record {w : FinitaryPerm ℕ+} {i : ℕ+}
    (hi : IsRecord w i) : w.suffixNonRecordCount i = w.nonRecordsFrom (i + 1) := by
  rw [suffixNonRecordCount, suffixNonRecords_eq_of_record hi, nonRecordsFrom_eq_card]

/-- Every suffix count of the identity permutation is zero. -/
@[simp]
theorem suffixNonRecordCount_one (i : ℕ+) : suffixNonRecordCount 1 i = 0 := by
  exact Nat.eq_zero_of_le_zero (by
    simpa only [nonRecordsFrom_one] using suffixNonRecordCount_le 1 i)

end FinitaryPerm
