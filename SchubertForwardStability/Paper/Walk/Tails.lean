import SchubertForwardStability.Paper.Walk.Basic

/-! # Tail maxima and record-count identities

## Main definitions

* `recordWalkMaxFrom`: the maximum on an interval starting at a positive position.
* `recordWalkExcess`: the excess of the support-bounded maximum over the second value.

## Main results

Nonempty tail maxima are attained, the excess is nonnegative, and the second walk
value is twice the ambient size plus one minus the two record counts.
-/

namespace RecordStability

open FinitaryPerm

open scoped Classical

/-- The finite maximum on positions from `i` through `n + 1`, with zero on an empty interval. -/
noncomputable def recordWalkMaxFrom (n : ℕ) (i : ℕ+) (u v : FinitaryPerm ℕ+) : ℤ :=
  (((positions (n + 1)).filter fun j => i ≤ j).sup fun j =>
    u.nonRecordsFrom j + v.nonRecordsFrom j + (j : ℕ) - 1 : ℕ)

/-- The excess of the support-bounded maximum over the walk's second value. -/
noncomputable def recordWalkExcess (u v : FinitaryPerm ℕ+) : ℤ :=
  recordWalkMax u v - recordWalk u v 2

/-- Every walk value in a tail interval is at most that interval's maximum. -/
theorem recordWalk_le_maxFrom {n : ℕ} (i : ℕ+) (u v : FinitaryPerm ℕ+) {j : ℕ+}
    (hij : i ≤ j) (hj : (j : ℕ) ≤ n + 1) :
    recordWalk u v j ≤ recordWalkMaxFrom n i u v := by
  rw [recordWalk_eq_nat]
  unfold recordWalkMaxFrom
  apply Int.ofNat_le.mpr
  exact Finset.le_sup (f := fun k : ℕ+ =>
    u.nonRecordsFrom k + v.nonRecordsFrom k + (k : ℕ) - 1)
    (Finset.mem_filter.mpr ⟨(mem_positions (n + 1) j).mpr hj, hij⟩)

/-- A nonempty tail interval has a position attaining its maximum. -/
theorem exists_recordWalk_eq_maxFrom {n : ℕ} (i : ℕ+) (u v : FinitaryPerm ℕ+)
    (hi : (i : ℕ) ≤ n + 1) :
    ∃ j : ℕ+, i ≤ j ∧ (j : ℕ) ≤ n + 1 ∧
      recordWalk u v j = recordWalkMaxFrom n i u v := by
  have hn : ((positions (n + 1)).filter fun j => i ≤ j).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨(mem_positions (n + 1) i).mpr hi, le_rfl⟩⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup _ hn
    (fun k : ℕ+ => u.nonRecordsFrom k + v.nonRecordsFrom k + (k : ℕ) - 1)
  obtain ⟨hjn, hij⟩ := Finset.mem_filter.mp hj
  refine ⟨j, hij, (mem_positions (n + 1) j).mp hjn, ?_⟩
  rw [recordWalk_eq_nat]
  unfold recordWalkMaxFrom
  exact congrArg (fun k : ℕ => (k : ℤ)) he.symm

/-- The excess of a tail maximum over its starting value is nonnegative. -/
theorem recordWalkMaxFrom_sub_nonneg {n : ℕ} (i : ℕ+) (u v : FinitaryPerm ℕ+)
    (hi : (i : ℕ) ≤ n + 1) : 0 ≤ recordWalkMaxFrom n i u v - recordWalk u v i :=
  sub_nonneg.mpr (recordWalk_le_maxFrom i u v le_rfl hi)

/-- The support-bounded walk excess is nonnegative. -/
theorem recordWalkExcess_nonneg (u v : FinitaryPerm ℕ+) : 0 ≤ recordWalkExcess u v := by
  have hm := u.one_le_forwardStability.trans (le_max_left _ v.forwardStability)
  apply sub_nonneg.mpr
  exact recordWalk_le_max u v (by change 2 ≤ _; omega)

/-- The second walk value is determined by the two ambient record counts. -/
theorem recordWalk_second {n : ℕ} (u v : FinitaryPerm ℕ+)
    (hu : IsSupported n u) (hv : IsSupported n v) :
    recordWalk u v 2 = 2 * (n : ℤ) + 1 -
      ((recordCount n u : ℤ) + (recordCount n v : ℤ)) := by
  have hu1 := recordCount_add_nonRecords u hu
  have hv1 := recordCount_add_nonRecords v hv
  have hu2 := nonRecordsFrom_succ u 1
  have hv2 := nonRecordsFrom_succ v 1
  rw [nonRecordIndicator_eq_zero (isRecord_first u), zero_add] at hu2
  rw [nonRecordIndicator_eq_zero (isRecord_first v), zero_add] at hv2
  change u.nonRecordsFrom 1 = u.nonRecordsFrom 2 at hu2
  change v.nonRecordsFrom 1 = v.nonRecordsFrom 2 at hv2
  rw [hu2] at hu1
  rw [hv2] at hv1
  unfold recordWalk
  change (u.nonRecordsFrom 2 : ℤ) + (v.nonRecordsFrom 2 : ℤ) + 2 - 1 = _
  omega

end RecordStability
