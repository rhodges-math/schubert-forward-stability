import SchubertForwardStability.Permutations.Statistics.SuffixPivot

/-! # Suffix counts before an increasing-tail exchange

## Main results

An exchange at an increasing-tail pivot preserves suffix non-records away from the
two exchanged positions. For an earlier suffix, the count decreases by one exactly
when all values before the start are below the pivot value.

## Implementation notes

The count comparison removes the two exchanged positions from both finite sets and
then restores their membership contributions separately.
-/

namespace FinitaryPerm

open scoped Classical

private theorem swap_window {i j r s k : ℕ+}
    (hir : i ≤ r) (his : i ≤ s) (hrj : r < j) (hsj : s < j)
    (hik : i ≤ k) (hkj : k < j) :
    i ≤ swap r s k ∧ swap r s k < j := by
  by_cases hkr : k = r
  · subst k
    simpa only [swap_apply_left] using And.intro his hsj
  · by_cases hks : k = s
    · subst k
      simpa only [swap_apply_right] using And.intro hir hrj
    · simpa only [swap_apply_of_ne hkr hks] using And.intro hik hkj

private theorem swap_twice (r s k : ℕ+) : swap r s (swap r s k) = k := by
  simpa only [swap_inv] using inv_apply_apply (swap r s) k

/-- Exchanging two earlier positions preserves the non-record predicate at a later position. -/
theorem suffixNonRecord_swap_before {w : FinitaryPerm ℕ+} {i j r s : ℕ+}
    (hir : i ≤ r) (his : i ≤ s) (hrj : r < j) (hsj : s < j) :
    IsSuffixNonRecord (w * swap r s) i j ↔ IsSuffixNonRecord w i j := by
  constructor
  · rintro ⟨k, hik, hkj, hv⟩
    obtain ⟨hiks, hksj⟩ := swap_window hir his hrj hsj hik hkj
    refine ⟨swap r s k, hiks, hksj, ?_⟩
    simpa only [mul_apply, swap_apply_of_ne (ne_of_gt hrj) (ne_of_gt hsj)] using hv
  · rintro ⟨k, hik, hkj, hv⟩
    obtain ⟨hiks, hksj⟩ := swap_window hir his hrj hsj hik hkj
    refine ⟨swap r s k, hiks, hksj, ?_⟩
    simpa only [mul_apply, swap_apply_of_ne (ne_of_gt hrj) (ne_of_gt hsj),
      swap_twice] using hv

/-- Exchanging two later positions preserves the non-record predicate at an earlier position. -/
theorem suffixNonRecord_swap_after {w : FinitaryPerm ℕ+} {i j r s : ℕ+}
    (hjr : j < r) (hjs : j < s) :
    IsSuffixNonRecord (w * swap r s) i j ↔ IsSuffixNonRecord w i j := by
  constructor <;> rintro ⟨k, hik, hkj, hv⟩
  · refine ⟨k, hik, hkj, ?_⟩
    simpa only [mul_apply, swap_apply_of_ne (ne_of_lt hjr) (ne_of_lt hjs),
      swap_apply_of_ne (ne_of_lt (hkj.trans hjr)) (ne_of_lt (hkj.trans hjs))] using hv
  · refine ⟨k, hik, hkj, ?_⟩
    simpa only [mul_apply, swap_apply_of_ne (ne_of_lt hjr) (ne_of_lt hjs),
      swap_apply_of_ne (ne_of_lt (hkj.trans hjr)) (ne_of_lt (hkj.trans hjs))] using hv

/-- A pivot exchange preserves an earlier suffix predicate away from the exchanged positions. -/
theorem IncreasingTailPivot.suffix_away {w : FinitaryPerm ℕ+} {i j r s : ℕ+}
    (h : IncreasingTailPivot w r s) (hi : i < r) (hjr : j ≠ r) (hjs : j ≠ s) :
    IsSuffixNonRecord (w * swap r s) i j ↔ IsSuffixNonRecord w i j := by
  rcases lt_or_gt_of_ne hjr with hjr | hrj
  · exact suffixNonRecord_swap_after hjr (hjr.trans h.start_lt)
  · rcases lt_or_gt_of_ne hjs with hjs | hsj
    · have hsmall := h.tail_strictMono hrj h.start_lt hjs
      constructor
      · intro _
        exact ⟨r, le_of_lt hi, hrj, hsmall.trans h.value_lt⟩
      · intro _
        refine ⟨r, le_of_lt hi, hrj, ?_⟩
        simpa only [mul_apply, swap_apply_of_ne (ne_of_gt hrj) (ne_of_lt hjs),
          swap_apply_left] using hsmall
    · exact suffixNonRecord_swap_before (le_of_lt hi)
        (le_of_lt (hi.trans h.start_lt)) hrj hsj

/-- The original pivot is a non-record in every suffix beginning before the start. -/
theorem IncreasingTailPivot.suffix_at_pivot {w : FinitaryPerm ℕ+} {i r s : ℕ+}
    (h : IncreasingTailPivot w r s) (hi : i < r) : IsSuffixNonRecord w i s :=
  ⟨r, le_of_lt hi, h.start_lt, h.value_lt⟩

/-- The exchanged pivot is a non-record exactly when the original start was a non-record. -/
theorem IncreasingTailPivot.exchanged_pivot {w : FinitaryPerm ℕ+} {i r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    IsSuffixNonRecord (w * swap r s) i s ↔ IsSuffixNonRecord w i r := by
  constructor
  · rintro ⟨k, hik, hks, hv⟩
    rw [mul_apply, swap_apply_right] at hv
    have hkr : k < r := by
      by_contra hn
      have hrk : r ≤ k := le_of_not_gt hn
      by_cases he : k = r
      · subst k
        rw [mul_apply, swap_apply_left] at hv
        exact (not_lt_of_gt h.value_lt) hv
      · have hrk' : r < k := lt_of_le_of_ne hrk (Ne.symm he)
        rw [mul_apply, swap_apply_of_ne he (ne_of_lt hks)] at hv
        exact (not_lt_of_gt
          ((h.tail_strictMono hrk' h.start_lt hks).trans h.value_lt)) hv
    refine ⟨k, hik, hkr, ?_⟩
    simpa only [mul_apply, swap_apply_of_ne (ne_of_lt hkr)
      (ne_of_lt (hkr.trans h.start_lt))] using hv
  · rintro ⟨k, hik, hkr, hv⟩
    refine ⟨k, hik, hkr.trans h.start_lt, ?_⟩
    simpa only [mul_apply, swap_apply_right, swap_apply_of_ne (ne_of_lt hkr)
      (ne_of_lt (hkr.trans h.start_lt))] using hv

/-- The exchanged start is a non-record iff the earlier prefix is not below the pivot value. -/
theorem IncreasingTailPivot.exchanged_start {w : FinitaryPerm ℕ+} {i r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    IsSuffixNonRecord (w * swap r s) i r ↔
      ¬∀ k : ℕ+, i ≤ k → k < r → w k < w s := by
  constructor
  · rintro ⟨k, hik, hkr, hv⟩ hall
    rw [mul_apply, swap_apply_left, mul_apply,
      swap_apply_of_ne (ne_of_lt hkr) (ne_of_lt (hkr.trans h.start_lt))] at hv
    exact (not_lt_of_gt (hall k hik hkr)) hv
  · intro hn
    push Not at hn
    obtain ⟨k, hik, hkr, hv⟩ := hn
    have hne : w k ≠ w s := fun he => (ne_of_lt (hkr.trans h.start_lt)) (w.injective he)
    refine ⟨k, hik, hkr, ?_⟩
    rw [mul_apply, swap_apply_left, mul_apply,
      swap_apply_of_ne (ne_of_lt hkr) (ne_of_lt (hkr.trans h.start_lt))]
    exact lt_of_le_of_ne hv (Ne.symm hne)

/-- The two suffix sets agree after their exchanged positions are removed. -/
theorem IncreasingTailPivot.erased_suffix_sets {w : FinitaryPerm ℕ+} {i r s : ℕ+}
    (h : IncreasingTailPivot w r s) (hi : i < r) :
    (((w * swap r s).suffixNonRecords i).erase r).erase s =
      ((w.suffixNonRecords i).erase r).erase s := by
  ext j
  simp only [Finset.mem_erase, mem_suffixNonRecords]
  constructor
  · rintro ⟨hjs, hjr, hj⟩
    exact ⟨hjs, hjr, (h.suffix_away hi hjr hjs).mp hj⟩
  · rintro ⟨hjs, hjr, hj⟩
    exact ⟨hjs, hjr, (h.suffix_away hi hjr hjs).mpr hj⟩

private theorem card_erase_indicator (t : Finset ℕ+) (a : ℕ+) :
    (t.erase a).card + (if a ∈ t then 1 else 0) = t.card := by
  by_cases ha : a ∈ t
  · simpa only [ha, ite_true] using Finset.card_erase_add_one ha
  · simp only [Finset.erase_eq_of_notMem ha, ha, ite_false, Nat.add_zero]

private theorem card_two_erase (t : Finset ℕ+) {r s : ℕ+} (hrs : r ≠ s) :
    ((t.erase r).erase s).card + (if r ∈ t then 1 else 0) +
      (if s ∈ t then 1 else 0) = t.card := by
  have hr := card_erase_indicator t r
  have hs := card_erase_indicator (t.erase r) s
  have hsr : s ≠ r := Ne.symm hrs
  have hmem : s ∈ t.erase r ↔ s ∈ t :=
    ⟨fun hj => (Finset.mem_erase.mp hj).2, fun hj => Finset.mem_erase.mpr ⟨hsr, hj⟩⟩
  simp only [hmem] at hs
  omega

/-- An earlier suffix loses one non-record exactly when its prefix is below the pivot value. -/
theorem IncreasingTailPivot.count_before {w : FinitaryPerm ℕ+} {i r s : ℕ+}
    (h : IncreasingTailPivot w r s) (hi : i < r) :
    w.suffixNonRecordCount i = (w * swap r s).suffixNonRecordCount i +
      if (∀ k : ℕ+, i ≤ k → k < r → w k < w s) then 1 else 0 := by
  let p := ∀ k : ℕ+, i ≤ k → k < r → w k < w s
  have hstart : r ∈ (w * swap r s).suffixNonRecords i ↔ ¬p := by
    simpa only [mem_suffixNonRecords, p] using h.exchanged_start (i := i)
  have hpivot : s ∈ (w * swap r s).suffixNonRecords i ↔ r ∈ w.suffixNonRecords i := by
    simpa only [mem_suffixNonRecords] using h.exchanged_pivot (i := i)
  have horig : s ∈ w.suffixNonRecords i :=
    (mem_suffixNonRecords w i s).mpr (h.suffix_at_pivot hi)
  have hw := card_two_erase (w.suffixNonRecords i) (ne_of_lt h.start_lt)
  have hv := card_two_erase ((w * swap r s).suffixNonRecords i) (ne_of_lt h.start_lt)
  rw [h.erased_suffix_sets hi] at hv
  rw [suffixNonRecordCount, suffixNonRecordCount]
  change _ = _ + if p then 1 else 0
  by_cases hp : p <;> by_cases hr : r ∈ w.suffixNonRecords i
  all_goals
    simp only [horig, hstart, hpivot, hp, hr, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false] at hw hv ⊢
    omega

end FinitaryPerm
