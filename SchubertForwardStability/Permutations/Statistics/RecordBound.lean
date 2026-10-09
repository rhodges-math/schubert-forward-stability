import SchubertForwardStability.Permutations.Statistics.Records

/-! # Forward bounds determined by non-record positions

## Main definitions

`nonRecordPositions` and `nonRecordBound` are the finite support and positive
maximum of the non-record indicator vector.

## Main results

The positive maximum of non-record positions equals individual forward stability.

## Implementation notes

Identity has empty non-record support but positive bound one.
-/

namespace FinitaryPerm

open scoped Classical

/-- The finite set of all non-record positions. -/
noncomputable def nonRecordPositions (w : FinitaryPerm ℕ+) : Finset ℕ+ :=
  (positions w.forwardStability).filter fun j => ¬IsRecord w j

/-- Non-record-position membership is exactly failure of the record condition. -/
@[simp]
theorem mem_nonRecordPositions (w : FinitaryPerm ℕ+) (j : ℕ+) :
    j ∈ w.nonRecordPositions ↔ ¬IsRecord w j := by
  simp only [nonRecordPositions, Finset.mem_filter, mem_positions]
  exact and_iff_right_of_imp fun h => le_of_not_gt fun hj => h (w.isRecord_above hj)

/-- The positive maximum of the non-record indicator support. -/
noncomputable def nonRecordBound (w : FinitaryPerm ℕ+) : ℕ :=
  max 1 (w.nonRecordPositions.sup PNat.val)

/-- Every non-record position lies below the positive non-record bound. -/
theorem nonRecord_le_bound {w : FinitaryPerm ℕ+} {j : ℕ+} (hj : ¬IsRecord w j) :
    (j : ℕ) ≤ w.nonRecordBound :=
  (Finset.le_sup ((mem_nonRecordPositions w j).mpr hj)).trans (le_max_right _ _)

/-- Non-record support cannot extend beyond the permutation's forward bound. -/
theorem nonRecordBound_le (w : FinitaryPerm ℕ+) : w.nonRecordBound ≤ w.forwardStability := by
  apply max_le w.one_le_forwardStability
  apply Finset.sup_le
  intro j hj
  exact (Finset.mem_filter.mp hj).1 |> (mem_positions _ _).mp

/-- The last moved position of a nonidentity permutation is not a record. -/
theorem lastMoved_not_record {w : FinitaryPerm ℕ+} (hw : w ≠ 1) :
    ∃ j : ℕ+, (j : ℕ) = w.forwardStability ∧ ¬IsRecord w j := by
  have hm : w.movedPoints.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h => hw ((movedPoints_eq_empty w).mp h))
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup w.movedPoints hm PNat.val
  have hb : w.supportBound = (j : ℕ) := hmax
  have hfs : w.forwardStability = (j : ℕ) := by
    rw [forwardStability, hb, max_eq_right (PNat.pos j)]
  have hfix : w j ≠ j := (mem_movedPoints w j).mp hj
  have hval : w j < j := by
    apply lt_of_le_of_ne
    · have h := w.isSupported_forwardStability.apply_le_iff j |>.mpr hfs.ge
      change (w j : ℕ) ≤ (j : ℕ)
      omega
    · exact hfix
  have hk : w⁻¹ j < j := by
    apply lt_of_le_of_ne
    · have h := w.isSupported_forwardStability.inv.apply_le_iff j |>.mpr hfs.ge
      change (w⁻¹ j : ℕ) ≤ (j : ℕ)
      omega
    · intro he
      have := congrArg w he
      exact hfix (by simpa only [apply_inv_apply] using this.symm)
  refine ⟨j, hfs.symm, ?_⟩
  intro hrec
  have := hrec (w⁻¹ j) hk
  rw [apply_inv_apply] at this
  exact (not_lt_of_gt hval) this

/-- The indicator-support maximum equals the least positive support bound. -/
theorem nonRecordBound_eq (w : FinitaryPerm ℕ+) : w.nonRecordBound = w.forwardStability := by
  apply le_antisymm (nonRecordBound_le w)
  by_cases hw : w = 1
  · subst w
    rw [forwardStability_one]
    exact le_max_left _ _
  · obtain ⟨j, hj, hn⟩ := lastMoved_not_record hw
    rw [← hj]
    exact nonRecord_le_bound hn

end FinitaryPerm
