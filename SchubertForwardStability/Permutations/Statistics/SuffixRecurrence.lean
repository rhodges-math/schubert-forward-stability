import SchubertForwardStability.Permutations.Statistics.PivotCovers
import SchubertForwardStability.Permutations.Statistics.SuffixAttainment

/-! # Finite pivot recurrence for suffix non-record counts

## Main results

The suffix count is the maximum of the pivot count with its starting-position increment
and the counts of the finite left-cover outputs.
-/

namespace FinitaryPerm

open scoped Classical

/-- The pivot contribution never exceeds the original suffix count. -/
theorem IncreasingTailPivot.count_pivot_le {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) (i : ℕ+) :
    (w * swap r s).suffixNonRecordCount i + (if i = r then 1 else 0) ≤
      w.suffixNonRecordCount i := by
  rcases lt_trichotomy i r with hi | he | hi
  · rw [ite_eq_right (ne_of_lt hi), Nat.add_zero, h.count_before hi]
    exact Nat.le_add_right _ _
  · subst i
    rw [ite_eq_left rfl, h.suffix_count, h.swapped_suffix_count]
    have hrs : (r : ℕ) < (s : ℕ) := h.start_lt
    omega
  · rw [ite_eq_right (ne_of_gt hi), h.count_after hi, h.swapped_count_after hi]

/-- Every finite left-cover contribution is bounded by the original suffix count. -/
theorem IncreasingTailPivot.count_transition_le {w : FinitaryPerm ℕ+} {q r s : ℕ+}
    (h : IncreasingTailPivot w r s) (i : ℕ+)
    (hq : q ∈ transitionPositions (w * swap r s) r) :
    ((w * swap r s) * swap q r).suffixNonRecordCount i ≤ w.suffixNonRecordCount i := by
  have hq' := (mem_transitionPositions _ _ _).mp hq
  by_cases hi : i < r
  · exact h.exchange_count_le hi hq'
  · have hqi : q < i := hq'.left_lt.trans_le (le_of_not_gt hi)
    exact (hq'.count_le_earlier hqi).trans
      ((Nat.le_add_right _ _).trans (h.count_pivot_le i))

private theorem count_le_max {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) (i : ℕ+) :
    w.suffixNonRecordCount i ≤
      max ((w * swap r s).suffixNonRecordCount i + (if i = r then 1 else 0))
        ((transitionPositions (w * swap r s) r).sup fun q =>
          ((w * swap r s) * swap q r).suffixNonRecordCount i) := by
  rcases lt_trichotomy i r with hi | he | hi
  · by_cases hp : ∀ k : ℕ+, i ≤ k → k < r → w k < w s
    · obtain ⟨q, _, hq, he⟩ := h.exists_exchange_attain hi hp
      have hmem := (mem_transitionPositions _ _ _).mpr hq
      have hle := Finset.le_sup (f := fun q =>
        ((w * swap r s) * swap q r).suffixNonRecordCount i) hmem
      rw [he] at hle
      exact hle.trans (le_max_right _ _)
    · rw [h.count_before hi, ite_eq_right hp, Nat.add_zero]
      exact (Nat.le_add_right _ _).trans (le_max_left _ _)
  · subst i
    have he : w.suffixNonRecordCount r =
        (w * swap r s).suffixNonRecordCount r + 1 := by
      rw [h.suffix_count, h.swapped_suffix_count]
      have hrs : (r : ℕ) < (s : ℕ) := h.start_lt
      omega
    rw [he, ite_eq_left rfl]
    exact le_max_left _ _
  · rw [h.count_after hi]
    exact Nat.zero_le _

/-- Suffix non-record counts satisfy the exact finite pivot maximum recurrence. -/
theorem IncreasingTailPivot.suffix_count_transition {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) (i : ℕ+) :
    w.suffixNonRecordCount i =
      max ((w * swap r s).suffixNonRecordCount i + (if i = r then 1 else 0))
        ((transitionPositions (w * swap r s) r).sup fun q =>
          ((w * swap r s) * swap q r).suffixNonRecordCount i) := by
  exact le_antisymm (count_le_max h i)
    (max_le (h.count_pivot_le i) (Finset.sup_le fun _ hq => h.count_transition_le i hq))

end FinitaryPerm
