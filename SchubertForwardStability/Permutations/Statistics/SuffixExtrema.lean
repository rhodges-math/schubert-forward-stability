import SchubertForwardStability.Permutations.Statistics.SuffixRecords

/-! # Suffix counts at the largest value

## Main results

A permutation whose positive support bound exceeds one moves its final supported position.
The suffix starting at the position of the largest supported value has exactly the number
of subsequent supported positions as non-records.

## Implementation notes

The largest supported value equals the positive forward-stability bound. Its position is
strictly earlier whenever that bound exceeds one.
-/

namespace FinitaryPerm

open scoped Classical

/-- A positive support bound exceeding one is a moved position. -/
theorem forwardStability_moved {w : FinitaryPerm ℕ+} (hw : 1 < w.forwardStability) :
    w ⟨w.forwardStability, w.one_le_forwardStability⟩ ≠
      ⟨w.forwardStability, w.one_le_forwardStability⟩ := by
  intro hfixed
  have hsmall : IsSupported (w.forwardStability - 1) w := by
    intro j hj
    by_cases he : (j : ℕ) = w.forwardStability
    · have hpos : j = ⟨w.forwardStability, w.one_le_forwardStability⟩ := PNat.eq he
      simpa only [hpos] using hfixed
    · exact w.isSupported_forwardStability j (by omega)
  have hbound := (forwardStability_le_iff w (by omega : 1 ≤ w.forwardStability - 1)).mpr
    hsmall
  omega

/-- At the largest supported value, every later supported position is a suffix non-record. -/
theorem suffixNonRecords_at_max {w : FinitaryPerm ℕ+} {i : ℕ+}
    (hi : (w i : ℕ) = w.forwardStability) :
    w.suffixNonRecords i = positions w.forwardStability \ positions (i : ℕ) := by
  ext j
  simp only [mem_suffixNonRecords, Finset.mem_sdiff, mem_positions]
  constructor
  · intro hj
    refine ⟨hj.le_forward, ?_⟩
    exact not_le_of_gt hj.start_lt
  · rintro ⟨hjn, hji⟩
    have hij : i < j := lt_of_not_ge hji
    refine ⟨i, le_rfl, hij, ?_⟩
    apply lt_of_le_of_ne
    · change (w j : ℕ) ≤ (w i : ℕ)
      rw [hi]
      exact (w.isSupported_forwardStability.apply_le_iff j).mpr hjn
    · exact fun he => (ne_of_gt hij) (w.injective he)

/-- The suffix at the largest supported value counts exactly all later supported positions. -/
theorem suffixNonRecordCount_at_max {w : FinitaryPerm ℕ+} {i : ℕ+}
    (hi : (w i : ℕ) = w.forwardStability) :
    w.suffixNonRecordCount i = w.forwardStability - (i : ℕ) := by
  have hin : (i : ℕ) ≤ w.forwardStability :=
    (w.isSupported_forwardStability.apply_le_iff i).mp (by omega)
  have hsubset : positions (i : ℕ) ⊆ positions w.forwardStability := by
    intro j hj
    exact (mem_positions _ j).mpr (((mem_positions _ j).mp hj).trans hin)
  rw [suffixNonRecordCount, suffixNonRecords_at_max hi,
    Finset.card_sdiff_of_subset hsubset, card_positions, card_positions]

/-- A nontrivial support bound is attained by a positive suffix-count candidate. -/
theorem exists_suffix_count_extreme {w : FinitaryPerm ℕ+}
    (hw : 1 < w.forwardStability) :
    ∃ i : ℕ+, (i : ℕ) < w.forwardStability ∧
      (i : ℕ) + w.suffixNonRecordCount i = w.forwardStability := by
  let m : ℕ+ := ⟨w.forwardStability, w.one_le_forwardStability⟩
  let i := w⁻¹ m
  have hvalue : w i = m := apply_inv_apply w m
  have hin : (i : ℕ) ≤ w.forwardStability :=
    (w.isSupported_forwardStability.apply_le_iff i).mp (by rw [hvalue]; rfl)
  have hne : (i : ℕ) ≠ w.forwardStability := by
    intro he
    have him : i = m := PNat.eq he
    apply forwardStability_moved hw
    simpa only [him] using hvalue
  refine ⟨i, lt_of_le_of_ne hin hne, ?_⟩
  rw [suffixNonRecordCount_at_max (by rw [hvalue]; rfl)]
  exact Nat.add_sub_of_le hin

end FinitaryPerm
