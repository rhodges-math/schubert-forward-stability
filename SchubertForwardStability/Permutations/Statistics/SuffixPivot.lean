import SchubertForwardStability.Permutations.Statistics.SuffixRecords

/-! # Suffix counts at a pivot of an increasing tail

## Main definitions

* `IncreasingTailPivot`: a position followed by an increasing tail and its final smaller value.

## Main results

The suffix count at the starting position is the distance to the pivot. Exchanging the
two positions decreases this count by one and preserves strict increase after the start.
Every suffix starting later has zero count, before and after the exchange.

## Implementation notes

The pivot conditions describe values and positions directly. Right multiplication by a
transposition exchanges the values at its two positive positions.
-/

namespace FinitaryPerm

open scoped Classical

/-- A starting position, an increasing tail, and its final value below the starting value. -/
structure IncreasingTailPivot (w : FinitaryPerm ℕ+) (r s : ℕ+) : Prop where
  /-- The pivot occurs strictly after the starting position. -/
  start_lt : r < s
  /-- Values strictly after the starting position increase. -/
  tail_strictMono : StrictMonoOn w {j : ℕ+ | r < j}
  /-- The pivot value is below the starting value. -/
  value_lt : w s < w r
  /-- Values strictly after the pivot exceed the starting value. -/
  above_lt : ∀ j : ℕ+, s < j → w r < w j

/-- In an increasing tail, a suffix non-record is exactly a value below its first value. -/
theorem suffixNonRecord_iff_of_tail {w : FinitaryPerm ℕ+} {i j : ℕ+}
    (htail : StrictMonoOn w {k : ℕ+ | i < k}) :
    IsSuffixNonRecord w i j ↔ i < j ∧ w j < w i := by
  constructor
  · intro h
    obtain ⟨k, hik, hkj, hvalue⟩ := h
    refine ⟨lt_of_le_of_lt hik hkj, ?_⟩
    by_cases he : k = i
    · simpa only [he] using hvalue
    · have hik' : i < k := lt_of_le_of_ne hik (Ne.symm he)
      exact False.elim ((not_lt_of_gt (htail hik' (lt_trans hik' hkj) hkj)) hvalue)
  · rintro ⟨hij, hvalue⟩
    exact ⟨i, le_rfl, hij, hvalue⟩

/-- Any suffix starting strictly inside an increasing tail has no non-records. -/
theorem suffixNonRecordCount_in_tail {w : FinitaryPerm ℕ+} {r i : ℕ+}
    (htail : StrictMonoOn w {j : ℕ+ | r < j}) (hi : r < i) :
    w.suffixNonRecordCount i = 0 := by
  rw [suffixNonRecordCount, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨k, hik, hkj, hvalue⟩ := (mem_suffixNonRecords w i j).mp hj
  have hrk : r < k := lt_of_lt_of_le hi hik
  exact (not_lt_of_gt (htail hrk (lt_trans hrk hkj) hkj)) hvalue

/-- Non-records at an increasing-tail pivot are exactly the positions through the pivot. -/
theorem IncreasingTailPivot.suffix_iff {w : FinitaryPerm ℕ+} {r s j : ℕ+}
    (h : IncreasingTailPivot w r s) :
    IsSuffixNonRecord w r j ↔ r < j ∧ j ≤ s := by
  rw [suffixNonRecord_iff_of_tail h.tail_strictMono]
  constructor
  · rintro ⟨hrj, hvalue⟩
    refine ⟨hrj, ?_⟩
    by_contra hjs
    exact (not_lt_of_gt (h.above_lt j (lt_of_not_ge hjs))) hvalue
  · rintro ⟨hrj, hjs⟩
    refine ⟨hrj, ?_⟩
    by_cases he : j = s
    · simpa only [he] using h.value_lt
    · exact (h.tail_strictMono hrj h.start_lt (lt_of_le_of_ne hjs he)).trans h.value_lt

/-- Exchanging the starting position with its pivot preserves increase throughout the tail. -/
theorem IncreasingTailPivot.swapped_tail {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    StrictMonoOn (w * swap r s) {j : ℕ+ | r < j} := by
  intro k hk j hj hkj
  by_cases hks : k = s
  · subst k
    rw [mul_apply, swap_apply_right, mul_apply,
      swap_apply_of_ne (ne_of_gt hj) (ne_of_gt hkj)]
    exact h.above_lt j hkj
  · by_cases hjs : j = s
    · subst j
      rw [mul_apply, swap_apply_of_ne (ne_of_gt hk) hks, mul_apply, swap_apply_right]
      exact (h.tail_strictMono hk h.start_lt hkj).trans h.value_lt
    · rw [mul_apply, swap_apply_of_ne (ne_of_gt hk) hks,
        mul_apply, swap_apply_of_ne (ne_of_gt hj) hjs]
      exact h.tail_strictMono hk hj hkj

/-- After the pivot exchange, the suffix non-records stop just before the pivot. -/
theorem IncreasingTailPivot.swapped_suffix_iff {w : FinitaryPerm ℕ+} {r s j : ℕ+}
    (h : IncreasingTailPivot w r s) :
    IsSuffixNonRecord (w * swap r s) r j ↔ r < j ∧ j < s := by
  have hstart : (w * swap r s) r = w s := by rw [mul_apply, swap_apply_left]
  rw [suffixNonRecord_iff_of_tail h.swapped_tail, hstart]
  constructor
  · rintro ⟨hrj, hvalue⟩
    refine ⟨hrj, ?_⟩
    by_contra hjs
    have hsj : s ≤ j := le_of_not_gt hjs
    by_cases he : j = s
    · rw [he, mul_apply, swap_apply_right] at hvalue
      exact (not_lt_of_gt h.value_lt) hvalue
    · have hsj' : s < j := lt_of_le_of_ne hsj (Ne.symm he)
      rw [mul_apply, swap_apply_of_ne (ne_of_gt hrj) he] at hvalue
      exact (not_lt_of_gt (h.value_lt.trans (h.above_lt j hsj'))) hvalue
  · rintro ⟨hrj, hjs⟩
    refine ⟨hrj, ?_⟩
    rw [mul_apply, swap_apply_of_ne (ne_of_gt hrj) (ne_of_lt hjs)]
    exact h.tail_strictMono hrj h.start_lt hjs

/-- The suffix non-record set at a pivot is the interval after the start through the pivot. -/
theorem IncreasingTailPivot.suffix_set {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    w.suffixNonRecords r = positions (s : ℕ) \ positions (r : ℕ) := by
  ext j
  simp only [mem_suffixNonRecords, h.suffix_iff, Finset.mem_sdiff, mem_positions]
  exact ⟨fun hj => ⟨hj.2, not_le_of_gt hj.1⟩,
    fun hj => ⟨lt_of_not_ge hj.2, hj.1⟩⟩

/-- The suffix count at an increasing-tail pivot is its distance from the start. -/
theorem IncreasingTailPivot.suffix_count {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    w.suffixNonRecordCount r = (s : ℕ) - (r : ℕ) := by
  have hsubset : positions (r : ℕ) ⊆ positions (s : ℕ) := by
    intro j hj
    exact (mem_positions _ j).mpr
      (((mem_positions _ j).mp hj).trans (le_of_lt h.start_lt))
  rw [suffixNonRecordCount, h.suffix_set,
    Finset.card_sdiff_of_subset hsubset, card_positions, card_positions]

/-- The exchanged suffix non-record set stops one position before the pivot. -/
theorem IncreasingTailPivot.swapped_suffix_set {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    (w * swap r s).suffixNonRecords r =
      positions ((s : ℕ) - 1) \ positions (r : ℕ) := by
  ext j
  simp only [mem_suffixNonRecords, h.swapped_suffix_iff, Finset.mem_sdiff, mem_positions]
  have hjpos := PNat.pos j
  have hspos := PNat.pos s
  change (r : ℕ) < (j : ℕ) ∧ (j : ℕ) < (s : ℕ) ↔
    (j : ℕ) ≤ (s : ℕ) - 1 ∧ ¬(j : ℕ) ≤ (r : ℕ)
  omega

/-- Exchanging an increasing-tail pivot decreases the starting suffix count by one. -/
theorem IncreasingTailPivot.swapped_suffix_count {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    (w * swap r s).suffixNonRecordCount r = (s : ℕ) - (r : ℕ) - 1 := by
  have hrs : (r : ℕ) < (s : ℕ) := h.start_lt
  have hsubset : positions (r : ℕ) ⊆ positions ((s : ℕ) - 1) := by
    intro j hj
    exact (mem_positions _ j).mpr (by
      have hjr := (mem_positions _ j).mp hj
      omega)
  rw [suffixNonRecordCount, h.swapped_suffix_set,
    Finset.card_sdiff_of_subset hsubset, card_positions, card_positions]
  omega

/-- All suffix counts strictly after an increasing-tail start vanish. -/
theorem IncreasingTailPivot.count_after {w : FinitaryPerm ℕ+} {r s i : ℕ+}
    (h : IncreasingTailPivot w r s) (hi : r < i) : w.suffixNonRecordCount i = 0 :=
  suffixNonRecordCount_in_tail h.tail_strictMono hi

/-- All suffix counts strictly after the exchanged increasing-tail start vanish. -/
theorem IncreasingTailPivot.swapped_count_after {w : FinitaryPerm ℕ+} {r s i : ℕ+}
    (h : IncreasingTailPivot w r s) (hi : r < i) :
    (w * swap r s).suffixNonRecordCount i = 0 :=
  suffixNonRecordCount_in_tail h.swapped_tail hi

end FinitaryPerm
